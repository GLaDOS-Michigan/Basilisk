include "messageInvariants.dfy"


module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Protocol bundle
ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  && CommitImpliesAllPreferYes(c, v)
  && LeaderVotesValid1(c, v)
  && LeaderTallyReflectsPreferences1(c, v)
}

// more like WF
ghost predicate LeaderVotesValid1(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall hostId | hostId in v.GetCoordinator(c).yesVotes
  :: 0 <= hostId < |c.participants|
}

ghost predicate CommitImpliesAllPreferYes(c: Constants, v: Variables)
  requires v.WF(c)
{
  CoordinatorDecidedCommit(c, v)
  ==>
  AllPreferYes(c)
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences1(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
{
  var n := |c.participants|;
  && (forall hostId | hostId in v.GetCoordinator(c).yesVotes  ::
      GetParticipantPreference(c, hostId) == Yes )
}


// User-level invariant
ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && MessageInv(c, v)
  && ProtocolInv(c, v)
  && Safety(c, v)
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  InvNextLeaderVotesValid(c, v, v');
  LeaderTallyReflectsPreferencesInductive(c, v, v');
  AC3Proof(c, v, v');
}

lemma InvNextLeaderVotesValid(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderVotesValid1(c, v')
{
  forall hostId | hostId in v'.GetCoordinator(c).yesVotes
  ensures 0 <= hostId < |c.participants| {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.CoordinatorStep? {
      if hostId in v.GetCoordinator(c).yesVotes {
        assert 0 <= hostId < |c.participants|;
      } else {
        assert 0 <= hostId < |c.participants|;
      }
    }
  }
}

lemma LeaderTallyReflectsPreferencesInductive(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderVotesValid1(c, v')
  ensures LeaderTallyReflectsPreferences1(c, v')
{}

lemma AC3Proof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures CommitImpliesAllPreferYes(c, v')
{
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v') {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.CoordinatorStep? {
        /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
        a Yes vote from all participants, including noVoter. This is a contradiction */
        var l, l' := v.GetCoordinator(c), v'.GetCoordinator(c);
        if l.decision.WONone? && l'.decision == WOSome(Commit) {
          YesVotesContainsAllParticipantsWhenFull(c, v);
          assert GetParticipantPreference(c, noVoter) == Yes;  // witness
          assert false;
        }
    }
  }
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables)
  requires Inv(c, v)
  requires |v.GetCoordinator(c).yesVotes| == |c.participants|
  ensures forall id | 0 <= id < |c.participants| :: id in v.GetCoordinator(c).yesVotes
{
  var l := v.GetCoordinator(c);
  forall id | 0 <= id < |c.participants|
  ensures id in l.yesVotes {
    if id !in l.yesVotes {
      SetLemma(l.yesVotes, id, |c.participants|);
      assert false;
    }
  }
}

lemma SetLemma(S: set<HostId>, e: HostId, size: int) 
  requires 0 <= e < size
  requires forall x | x in S :: 0 <= x < size
  requires e !in S
  ensures |S| < size
{
  var fullSet := set x | 0 <= x < size;
  SetComprehensionSize(size);
  SetContainmentCardinalityStrict(S, fullSet);
}
}
