include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

// All msg have a valid source
ghost predicate ValidMessages(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs
  ::
  if msg.Decide? then 0 <= msg.Src() < |c.coordinator|
  else if msg.Vote? then 0 <= msg.Src() < |c.participants|
  else true
}

ghost predicate {:opaque} ExistingMessage(v: Variables, msg: Message) {
  msg in v.network.sentMsgs
}

ghost predicate SendDecideValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Decide?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && CoordinatorHost.SendDecide(c.coordinator[msg.Src()], v.History(i).coordinator[msg.Src()], v.History(i+1).coordinator[msg.Src()], msg)
  )
}

ghost predicate SendVoteValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && ParticipantHost.SendVote(c.participants[msg.Src()], v.History(i).participants[msg.Src()], v.History(i+1).participants[msg.Src()], msg)
  )
}

ghost predicate {:opaque} CoordinatorHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.coordinator|
    && v.History(i).coordinator[idx] !=  v.History(0).coordinator[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).coordinator[idx] != v.History(j+1).coordinator[idx])
       && (v.History(j+1).coordinator[idx] == v.History(i).coordinator[idx])
       && CoordinatorHost.NextStep(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} CoordinatorHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).coordinator[idx] != v.History(j+1).coordinator[idx])
       && (v.History(j+1).coordinator[idx] == v.History(i).coordinator[idx])
       && CoordinatorHost.NextStep(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate {:opaque} ParticipantHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.participants|
    && v.History(i).participants[idx] !=  v.History(0).participants[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).participants[idx] != v.History(j+1).participants[idx])
       && (v.History(j+1).participants[idx] == v.History(i).participants[idx])
       && ParticipantHost.NextStep(c.participants[idx], v.History(j).participants[idx], v.History(j+1).participants[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} ParticipantHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.participants|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).participants[idx] != v.History(j+1).participants[idx])
       && (v.History(j+1).participants[idx] == v.History(i).participants[idx])
       && ParticipantHost.NextStep(c.participants[idx], v.History(j).participants[idx], v.History(j+1).participants[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && ValidMessages(c, v)
  && SendDecideValidity(c, v)
  && SendVoteValidity(c, v)
  && CoordinatorHostReceiveValidity(c, v)
  && ParticipantHostReceiveValidity(c, v)
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_CoordinatorHostReceiveValidity();
  reveal_ParticipantHostReceiveValidity();
}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')

{
  InvNextValidVariables(c, v, v');
  InvNextSendDecideValidity(c, v, v');
  InvNextSendVoteValidity(c, v, v');
  InvNextCoordinatorHostReceiveValidity(c, v, v');
  InvNextParticipantHostReceiveValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/

lemma InvNextSendDecideValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendDecideValidity(c, v)
  requires Next(c, v, v')
  ensures SendDecideValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Decide?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && CoordinatorHost.SendDecide(c.coordinator[msg.Src()], v'.History(i).coordinator[msg.Src()], v'.History(i+1).coordinator[msg.Src()], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert CoordinatorHost.SendDecide(c.coordinator[msg.Src()], v'.History(i).coordinator[msg.Src()], v'.History(i+1).coordinator[msg.Src()], msg);
    }
  }
}

lemma InvNextSendVoteValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendVoteValidity(c, v)
  requires Next(c, v, v')
  ensures SendVoteValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Vote?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && ParticipantHost.SendVote(c.participants[msg.Src()], v'.History(i).participants[msg.Src()], v'.History(i+1).participants[msg.Src()], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ParticipantHost.SendVote(c.participants[msg.Src()], v'.History(i).participants[msg.Src()], v'.History(i+1).participants[msg.Src()], msg);
    }
  }
}

lemma CoordinatorHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: CoordinatorHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires CoordinatorHostReceiveValidity(c, v)
  requires 0 <= idx < |c.coordinator|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).coordinator[idx] != v.History(0).coordinator[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).coordinator[idx] != v.History(j+1).coordinator[idx]
  ensures v.History(j+1).coordinator[idx] == v.History(i).coordinator[idx]
  ensures CoordinatorHost.NextStep(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_CoordinatorHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).coordinator[idx] != v.History(j+1).coordinator[idx])
      && (v.History(j+1).coordinator[idx] == v.History(i).coordinator[idx])
      && CoordinatorHost.NextStep(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextCoordinatorHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires CoordinatorHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures CoordinatorHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.coordinator|
    && v'.History(i).coordinator[idx] != v'.History(0).coordinator[idx]
  ensures
    CoordinatorHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert CoordinatorHostReceiveValidityPost(c, v', i, idx) by {
       reveal_CoordinatorHostReceiveValidity();
       reveal_CoordinatorHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).coordinator[idx] == v'.History(i).coordinator[idx] {
        var k, step, msgOps := CoordinatorHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).coordinator[idx] != v'.History(k+1).coordinator[idx];
        assert v'.History(k+1).coordinator[idx] == v'.History(i).coordinator[idx];
        assert CoordinatorHost.NextStep(c.coordinator[idx], v'.History(k).coordinator[idx], v'.History(k+1).coordinator[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).coordinator[idx] != v'.History(i).coordinator[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).coordinator[idx] == v'.History(i).coordinator[idx];
      }
      assert CoordinatorHostReceiveValidityPost(c, v', i, idx) by {
       reveal_CoordinatorHostReceiveValidity();
       reveal_CoordinatorHostReceiveValidityPost();
      }
    }
  }
  assert CoordinatorHostReceiveValidity(c, v') by {
    reveal_CoordinatorHostReceiveValidity();
    reveal_CoordinatorHostReceiveValidityPost();
  }
}

lemma ParticipantHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: ParticipantHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires ParticipantHostReceiveValidity(c, v)
  requires 0 <= idx < |c.participants|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).participants[idx] != v.History(0).participants[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).participants[idx] != v.History(j+1).participants[idx]
  ensures v.History(j+1).participants[idx] == v.History(i).participants[idx]
  ensures ParticipantHost.NextStep(c.participants[idx], v.History(j).participants[idx], v.History(j+1).participants[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_ParticipantHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).participants[idx] != v.History(j+1).participants[idx])
      && (v.History(j+1).participants[idx] == v.History(i).participants[idx])
      && ParticipantHost.NextStep(c.participants[idx], v.History(j).participants[idx], v.History(j+1).participants[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextParticipantHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ParticipantHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures ParticipantHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.participants|
    && v'.History(i).participants[idx] != v'.History(0).participants[idx]
  ensures
    ParticipantHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert ParticipantHostReceiveValidityPost(c, v', i, idx) by {
       reveal_ParticipantHostReceiveValidity();
       reveal_ParticipantHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).participants[idx] == v'.History(i).participants[idx] {
        var k, step, msgOps := ParticipantHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).participants[idx] != v'.History(k+1).participants[idx];
        assert v'.History(k+1).participants[idx] == v'.History(i).participants[idx];
        assert ParticipantHost.NextStep(c.participants[idx], v'.History(k).participants[idx], v'.History(k+1).participants[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).participants[idx] != v'.History(i).participants[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).participants[idx] == v'.History(i).participants[idx];
      }
      assert ParticipantHostReceiveValidityPost(c, v', i, idx) by {
       reveal_ParticipantHostReceiveValidity();
       reveal_ParticipantHostReceiveValidityPost();
      }
    }
  }
  assert ParticipantHostReceiveValidity(c, v') by {
    reveal_ParticipantHostReceiveValidity();
    reveal_ParticipantHostReceiveValidityPost();
  }
}

/***************************************************************************************
*                                  Skolemizations                                      *
***************************************************************************************/

lemma SendDecideSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendDecideValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Decide?
  ensures v.ValidHistoryIdxStrict(i)
  ensures CoordinatorHost.SendDecide(c.coordinator[msg.Src()], v.History(i).coordinator[msg.Src()], v.History(i+1).coordinator[msg.Src()], msg)
{
  i :|
      && v.ValidHistoryIdxStrict(i)
      && CoordinatorHost.SendDecide(c.coordinator[msg.Src()], v.History(i).coordinator[msg.Src()], v.History(i+1).coordinator[msg.Src()], msg);
}

lemma SendVoteSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendVoteValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Vote?
  ensures v.ValidHistoryIdxStrict(i)
  ensures ParticipantHost.SendVote(c.participants[msg.Src()], v.History(i).participants[msg.Src()], v.History(i+1).participants[msg.Src()], msg)
{
  i :|
      && v.ValidHistoryIdxStrict(i)
      && ParticipantHost.SendVote(c.participants[msg.Src()], v.History(i).participants[msg.Src()], v.History(i+1).participants[msg.Src()], msg);
}

ghost predicate ReceiveVoteNoWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: HostId)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
{
  && a1 in v.History(i).coordinator[idx].noVotes.s
  && (v.History(i).coordinator[idx].noVotes != v.History(0).coordinator[idx].noVotes)
}

lemma ReceiveVoteNoStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: HostId)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires CoordinatorHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
  requires ReceiveVoteNoWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceiveVoteNoWitnessCondition(c, v, j, idx, a1)
  ensures ReceiveVoteNoWitnessCondition(c, v, j+1, idx, a1)
  ensures CoordinatorHost.ReceiveVoteNo(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := CoordinatorHostReceiveSkolemization(c, v, i, idx);
  if !ReceiveVoteNoWitnessCondition(c, v, xj, idx, a1) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceiveVoteNoStepSkolemization(c, v, xj, idx, a1);
  }
}

ghost predicate ReceiveVoteYesWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: HostId)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
{
  && a1 in v.History(i).coordinator[idx].yesVotes.s
  && (v.History(i).coordinator[idx].yesVotes != v.History(0).coordinator[idx].yesVotes)
}

lemma ReceiveVoteYesStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: HostId)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires CoordinatorHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
  requires ReceiveVoteYesWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceiveVoteYesWitnessCondition(c, v, j, idx, a1)
  ensures ReceiveVoteYesWitnessCondition(c, v, j+1, idx, a1)
  ensures CoordinatorHost.ReceiveVoteYes(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := CoordinatorHostReceiveSkolemization(c, v, i, idx);
  if !ReceiveVoteYesWitnessCondition(c, v, xj, idx, a1) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceiveVoteYesStepSkolemization(c, v, xj, idx, a1);
  }
}

ghost predicate MakeDecisionWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Option<Decision>)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
{
  && a1 == v.History(i).coordinator[idx].decision
  && (v.History(i).coordinator[idx].decision != v.History(0).coordinator[idx].decision)
}

lemma MakeDecisionStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: Option<Decision>)
  returns (j: nat, step: CoordinatorHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires CoordinatorHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.coordinator|
  requires MakeDecisionWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !MakeDecisionWitnessCondition(c, v, j, idx, a1)
  ensures MakeDecisionWitnessCondition(c, v, j+1, idx, a1)
  ensures CoordinatorHost.NextStep(c.coordinator[idx], v.History(j).coordinator[idx], v.History(j+1).coordinator[idx], step, msgOps)
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := CoordinatorHostReceiveSkolemization(c, v, i, idx);
  if !MakeDecisionWitnessCondition(c, v, xj, idx, a1) {
    j, step, msgOps := xj, xstep, xmsgOps;
  } else {
    j, step, msgOps := MakeDecisionStepSkolemization(c, v, xj, idx, a1);
  }
}

ghost predicate ReceiveDecideWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Option<Decision>)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.participants|
{
  && a1 == v.History(i).participants[idx].decision
  && (v.History(i).participants[idx].decision != v.History(0).participants[idx].decision)
}

lemma ReceiveDecideStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: Option<Decision>)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires ParticipantHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.participants|
  requires ReceiveDecideWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceiveDecideWitnessCondition(c, v, j, idx, a1)
  ensures ReceiveDecideWitnessCondition(c, v, j+1, idx, a1)
  ensures ParticipantHost.ReceiveDecide(c.participants[idx], v.History(j).participants[idx], v.History(j+1).participants[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := ParticipantHostReceiveSkolemization(c, v, i, idx);
  if !ReceiveDecideWitnessCondition(c, v, xj, idx, a1) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceiveDecideStepSkolemization(c, v, xj, idx, a1);
  }
}

} // end module MessageInvariants
