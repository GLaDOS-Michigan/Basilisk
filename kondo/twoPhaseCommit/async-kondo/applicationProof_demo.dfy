/// This file is auto-generated from KondoPrototypes/twoPhaseCommit/centralized/applicationProof.dfy
/// Generated 04/02/2024 16:50 Pacific Standard Time

/// It has been modified to fill the the body of lemma InvNextAC3

include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module Proof {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary
  import opened DistributedSystem
  import opened MonotonicityInvariants
  import opened MessageInvariants
  import opened Obligations

ghost predicate LeaderVotesValid1(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall hostId: int, i: nat
 {:trigger hostId in v.History(i).GetCoordinator(c).yesVotes}
 | v.ValidHistoryIdx(i) && hostId in v.History(i).GetCoordinator(c).yesVotes :: 
    0 <= hostId &&
    hostId < |c.participants|
}

ghost predicate LeaderVotesValid2(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall hostId: int, i: nat
 {:trigger hostId in v.History(i).GetCoordinator(c).noVotes}
 | v.ValidHistoryIdx(i) && hostId in v.History(i).GetCoordinator(c).noVotes :: 
    0 <= hostId &&
    hostId < |c.participants|
}

ghost predicate LeaderTallyReflectsPreferences1(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
  decreases c, v
{
  forall i :: v.ValidHistoryIdx(i) ==> (
    ghost var n: int := |c.participants|;
    true &&
    forall hostId: int
 {:trigger GetParticipantPreference(c, hostId), v.ValidHistoryIdx(i)} {:trigger hostId in v.History(i).GetCoordinator(c).yesVotes}
 | hostId in v.History(i).GetCoordinator(c).yesVotes :: 
      GetParticipantPreference(c, hostId) == Yes
  )
}

ghost predicate LeaderTallyReflectsPreferences2(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid2(c, v)
  decreases c, v
{
  forall i :: v.ValidHistoryIdx(i) ==> (
    ghost var n: int := |c.participants|;
    true &&
    forall hostId: int
 {:trigger GetParticipantPreference(c, hostId), v.ValidHistoryIdx(i)} {:trigger hostId in v.History(i).GetCoordinator(c).noVotes}
 | hostId in v.History(i).GetCoordinator(c).noVotes :: 
      GetParticipantPreference(c, hostId) == No
  )
}

ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderVotesValid1(c, v)
  && LeaderVotesValid2(c, v)
  && LeaderTallyReflectsPreferences1(c, v)
  && LeaderTallyReflectsPreferences2(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ProtocolInv(c, v)
  && Safety(c, v)
}

/***************************************************************************************
*                                    Obligations                                       *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMonotonicityInv(c, v);
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  InvNextLeaderTallyReflectsPreferences(c, v, v');
  InvNextAC1(c, v, v');
  InvNextAC3(c, v, v');
  InvNextAC4(c, v, v');
}


/***************************************************************************************
*                                   InvNext Proofs                                     *
***************************************************************************************/

lemma InvNextAC1(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC1(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderTallyReflectsPreferences(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ProtocolInv(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

// modified: 19 lines
lemma InvNextAC3(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AC3Contrapos(c, v')
{
  AC3ContraposLemma(c, v);
  VariableNextProperties(c, v, v');
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v'.Last()) {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    if dsStep.CoordinatorHostStep? {
        /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
        a Yes vote from all participants, including noVoter. This is a contradiction */
        var l, l' := v.Last().GetCoordinator(c), v'.Last().GetCoordinator(c);
        if l.decision.WONone? && l'.decision == WOSome(Commit) {
          YesVotesContainsAllParticipantsWhenFull(c, v);
          assert noVoter in v.Last().GetCoordinator(c).yesVotes;
        }
    }
  }
}

lemma InvNextAC4(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC4(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}


/***************************************************************************************
*                                    Helper Lemmas                                     *
***************************************************************************************/

lemma AC3ContraposLemma(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures AC3Contrapos(c, v)
  decreases c, v
{
  if !AllPreferYes(c) && CoordinatorHasDecided(c, v.Last()) {
    assert v.Last().GetCoordinator(c).decision.value != Commit;
  }
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables)
  requires Inv(c, v)
  requires |v.Last().GetCoordinator(c).yesVotes| == |c.participants|
  ensures forall id: int
 
 | 0 <= id < |c.participants| :: id in v.Last().GetCoordinator(c).yesVotes
  decreases c, v
{
  ghost var l := v.Last().GetCoordinator(c);
  forall id: int

 | 0 <= id < |c.participants|
    ensures id in l.yesVotes
  {
    if id !in l.yesVotes {
      SetLemma(l.yesVotes, id, |c.participants|);
      assert false;
    }
  }
}

lemma SetLemma(S: set<HostId>, e: HostId, size: int)
  requires 0 <= e < size
  requires forall x: int
 
 | x in S :: 0 <= x && x < size
  requires e !in S
  ensures |S| < size
  decreases S, e, size
{
  ghost var fullSet := set x: int | 0 <= x < size;
  SetComprehensionSize(size);
  SetContainmentCardinalityStrict(S, fullSet);
}


} // end module Proof
