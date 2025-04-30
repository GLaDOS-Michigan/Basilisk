include "spec.dfy"

module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderVotesValid1(c, v)
  && LeaderVotesValid2(c, v)
  && LeaderTallyReflectsPreferences1(c, v)
  && LeaderTallyReflectsPreferences2(c, v)
}

ghost predicate LeaderVotesValid1(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall hostId | hostId in v.GetCoordinator(c).yesVotes.s
  :: 0 <= hostId < |c.participants|
}

ghost predicate LeaderVotesValid2(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall hostId | hostId in v.GetCoordinator(c).noVotes.s
  :: 0 <= hostId < |c.participants|
}

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences1(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid1(c, v)
{
  var n := |c.participants|;
  && (forall hostId | hostId in v.GetCoordinator(c).yesVotes.s  ::
      GetParticipantPreference(c, hostId) == Yes )
}

// Leader's local tally reflect participant preferences
// Auto-triggers: {GetParticipantPreference(c, hostId)}, {hostId in v.GetCoordinator(c).noVotes.s}
ghost predicate LeaderTallyReflectsPreferences2(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid2(c, v)
{
  var n := |c.participants|;
  && (forall hostId | hostId in v.GetCoordinator(c).noVotes.s ::
      GetParticipantPreference(c, hostId) == No )
}

// User-level invariant
ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ApplicationInv(c, v)
  && Safety(c, v)
}

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
  InvNextLeaderTallyReflectsPreferences(c, v, v');
  InvNextAC1(c, v, v');
  InvNextAC3(c, v, v');
  InvNextAC4(c, v, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

lemma InvNextAC1(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC1(c, v')
{}


lemma InvNextLeaderTallyReflectsPreferences(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderTallyReflectsPreferences1(c, v')
  ensures LeaderTallyReflectsPreferences2(c, v')
{}

lemma InvNextAC3(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC3(c, v')
{
  forall pidx | c.ValidParticipantId(pidx) && ParticipantDecidedCommit(c, v', pidx)
  ensures AllPreferYes(c) 
  {
    if ! AllPreferYes(c) && CoordinatorHasDecided(c, v') {
      var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
      var sysStep :| NextStep(c, v, v', sysStep);
      if sysStep.DecideStep? {
        var decision := sysStep.transmit.m.decision;
        if decision == Commit {
          YesVotesContainsAllParticipantsWhenFull(c, v);
          assert GetParticipantPreference(c, noVoter) == Yes;  // witness
          assert false;
        }
      }
    }
  }
}

lemma InvNextAC4(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures SafetyAC4(c, v')
{}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables)
  requires Inv(c, v)
  requires |v.GetCoordinator(c).yesVotes.s| >= |c.participants|
  ensures forall id | 0 <= id < |c.participants| :: id in v.GetCoordinator(c).yesVotes.s
{
  var l := v.GetCoordinator(c);
  forall id | 0 <= id < |c.participants|
  ensures id in l.yesVotes.s {
    if id !in l.yesVotes.s {
      SetLemma(l.yesVotes.s, id, |c.participants|);
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

// END SAFETY PROOF
}

