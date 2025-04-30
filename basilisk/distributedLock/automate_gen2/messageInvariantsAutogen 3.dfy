/// This file is auto-generated from /Users/nudzhang/Documents/2025/osdi/artifact.nosync/basilisk/distributedLock/automate_gen2/distributedSystem.dfy
/// Generated 04/29/2025 09:11 Pacific Standard Time
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
  if msg.Grant? then 0 <= msg.Src() < |c.hosts|
  else true
}

ghost predicate {:opaque} ExistingMessage(v: Variables, msg: Message) {
  msg in v.network.sentMsgs
}

ghost predicate SendGrantValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Grant?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && Host.SendGrant(c.hosts[msg.Src()], v.History(i).hosts[msg.Src()], v.History(i+1).hosts[msg.Src()], msg)
  )
}

ghost predicate {:opaque} HostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.hosts|
    && v.History(i).hosts[idx] !=  v.History(0).hosts[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).hosts[idx] != v.History(j+1).hosts[idx])
       && (v.History(j+1).hosts[idx] == v.History(i).hosts[idx])
       && Host.NextStep(c.hosts[idx], v.History(j).hosts[idx], v.History(j+1).hosts[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} HostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).hosts[idx] != v.History(j+1).hosts[idx])
       && (v.History(j+1).hosts[idx] == v.History(i).hosts[idx])
       && Host.NextStep(c.hosts[idx], v.History(j).hosts[idx], v.History(j+1).hosts[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && ValidMessages(c, v)
  && SendGrantValidity(c, v)
  && HostReceiveValidity(c, v)
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_HostReceiveValidity();
}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')

{
  InvNextValidVariables(c, v, v');
  InvNextSendGrantValidity(c, v, v');
  InvNextHostReceiveValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/

lemma InvNextSendGrantValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendGrantValidity(c, v)
  requires Next(c, v, v')
  ensures SendGrantValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Grant?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && Host.SendGrant(c.hosts[msg.Src()], v'.History(i).hosts[msg.Src()], v'.History(i+1).hosts[msg.Src()], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert Host.SendGrant(c.hosts[msg.Src()], v'.History(i).hosts[msg.Src()], v'.History(i+1).hosts[msg.Src()], msg);
    }
  }
}

lemma HostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: Host.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires HostReceiveValidity(c, v)
  requires 0 <= idx < |c.hosts|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).hosts[idx] != v.History(0).hosts[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).hosts[idx] != v.History(j+1).hosts[idx]
  ensures v.History(j+1).hosts[idx] == v.History(i).hosts[idx]
  ensures Host.NextStep(c.hosts[idx], v.History(j).hosts[idx], v.History(j+1).hosts[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_HostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).hosts[idx] != v.History(j+1).hosts[idx])
      && (v.History(j+1).hosts[idx] == v.History(i).hosts[idx])
      && Host.NextStep(c.hosts[idx], v.History(j).hosts[idx], v.History(j+1).hosts[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires HostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures HostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.hosts|
    && v'.History(i).hosts[idx] != v'.History(0).hosts[idx]
  ensures
    HostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert HostReceiveValidityPost(c, v', i, idx) by {
       reveal_HostReceiveValidity();
       reveal_HostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).hosts[idx] == v'.History(i).hosts[idx] {
        var k, step, msgOps := HostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).hosts[idx] != v'.History(k+1).hosts[idx];
        assert v'.History(k+1).hosts[idx] == v'.History(i).hosts[idx];
        assert Host.NextStep(c.hosts[idx], v'.History(k).hosts[idx], v'.History(k+1).hosts[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).hosts[idx] != v'.History(i).hosts[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).hosts[idx] == v'.History(i).hosts[idx];
      }
      assert HostReceiveValidityPost(c, v', i, idx) by {
       reveal_HostReceiveValidity();
       reveal_HostReceiveValidityPost();
      }
    }
  }
  assert HostReceiveValidity(c, v') by {
    reveal_HostReceiveValidity();
    reveal_HostReceiveValidityPost();
  }
}

/***************************************************************************************
*                                  Skolemizations                                      *
***************************************************************************************/

lemma SendGrantSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendGrantValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Grant?
  ensures v.ValidHistoryIdxStrict(i)
  ensures Host.SendGrant(c.hosts[msg.Src()], v.History(i).hosts[msg.Src()], v.History(i+1).hosts[msg.Src()], msg)
{
  i :|
      && v.ValidHistoryIdxStrict(i)
      && Host.SendGrant(c.hosts[msg.Src()], v.History(i).hosts[msg.Src()], v.History(i+1).hosts[msg.Src()], msg);
}

ghost predicate ReceiveGrantStepWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: nat)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && a1 == v.History(i).hosts[idx].myEpoch
  && (v.History(i).hosts[idx].myEpoch != v.History(0).hosts[idx].myEpoch)
}

lemma ReceiveGrantStepStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: nat)
  returns (j: nat, step: Host.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires HostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
  requires ReceiveGrantStepWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceiveGrantStepWitnessCondition(c, v, j, idx, a1)
  ensures ReceiveGrantStepWitnessCondition(c, v, j+1, idx, a1)
  ensures Host.NextStep(c.hosts[idx], v.History(j).hosts[idx], v.History(j+1).hosts[idx], step, msgOps)
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := HostReceiveSkolemization(c, v, i, idx);
  if !ReceiveGrantStepWitnessCondition(c, v, xj, idx, a1) {
    j, step, msgOps := xj, xstep, xmsgOps;
  } else {
    j, step, msgOps := ReceiveGrantStepStepSkolemization(c, v, xj, idx, a1);
  }
}

} // end module MessageInvariants
