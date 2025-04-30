include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module TwoPCInvariantProof {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations

ghost predicate RegularInvs(c: Constants, v: Variables) {
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ValidVariables(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && RegularInvs(c, v)
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
{
  VariableNextProperties(c, v, v');
  MessageInvInductive(c, v, v');
  MonotonicityInvInductive(c, v, v');
  AC1Proof(c, v');
  AC3Proof(c, v');
  AC4Proof(c, v');
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

// Leader's local tally reflect participant preferences
ghost predicate LeaderTallyReflectsPreferences(c: Constants, v: Variables)
  requires v.WF(c)
{
  && (forall hostId | hostId in v.Last().GetCoordinator(c).yesVotes.s ::
      0 <= hostId < |c.participants| && GetParticipantPreference(c, hostId) == Yes )
  && (forall hostId | hostId in v.Last().GetCoordinator(c).noVotes.s ::
        0 <= hostId < |c.participants| && GetParticipantPreference(c, hostId) == No )
}

lemma InvImpliesLeaderTallyReflectsPreferences(c: Constants, v: Variables) 
  requires RegularInvs(c, v)
  ensures LeaderTallyReflectsPreferences(c, v)
{
  var i := |v.history|-1;
  var n := |c.participants|;
  reveal_ValidHistory();
  forall hostId | hostId in v.Last().GetCoordinator(c).yesVotes.s
  ensures 0 <= hostId < n && GetParticipantPreference(c, hostId) == Yes {
    var j, msg := ReceiveVoteYesStepSkolemization(c, v, i, 0, hostId);
  }

  forall hostId | hostId in v.Last().GetCoordinator(c).noVotes.s
  ensures 0 <= hostId < n && GetParticipantPreference(c, hostId) == No {
    var j, msg := ReceiveVoteNoStepSkolemization(c, v, i, 0, hostId);
  }
}

lemma AC1Proof(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  ensures SafetyAC1(c, v)
{
  forall idx: HostId | c.ValidParticipantId(idx) && PartipantHasDecided(c, v.Last(), idx)
  ensures v.Last().GetCoordinator(c).decision == v.Last().participants[idx].decision {
    reveal_ValidHistory();
    var j, decideMsg := ReceiveDecideStepSkolemization(c, v, |v.history|-1, idx, v.Last().participants[idx].decision);
  }
}

lemma AC3Proof(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  ensures SafetyAC3(c, v)
{
  // We prove the contrapositive of AC3
  // Suppose not everyone preferred yes, and some participant has decided Commit.
  // Then we arrive at a contradiction
  forall pidx: nat | c.ValidParticipantId(pidx) && ParticipantDecidedCommit(c, v.Last(), pidx)
  ensures AllPreferYes(c) {
    if !AllPreferYes(c) {
      reveal_ValidHistory();
      var _, commitMsg := ReceiveDecideStepSkolemization(c, v, |v.history|-1, pidx, v.Last().participants[pidx].decision);
      var j := SendDecideSkolemization(c, v, commitMsg);
      var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
      YesVotesContainsAllParticipantsWhenFull(c, v, j);
      InvImpliesLeaderTallyReflectsPreferences(c, v);
      assert noVoter in v.Last().GetCoordinator(c).yesVotes.s;  // trigger
      // assert false;
    }
  }
}


lemma AC4Proof(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  ensures SafetyAC4(c, v)
{
  forall pidx: nat | c.ValidParticipantId(pidx) && PartipantHasDecided(c, v.Last(), pidx) && AllPreferYes(c) 
  ensures ParticipantDecidedCommit(c, v.Last(), pidx) {
    if !ParticipantDecidedCommit(c, v.Last(), pidx) {
      reveal_ValidHistory();
      var _, abortMsg := ReceiveDecideStepSkolemization(c, v, |v.history|-1, pidx, v.Last().participants[pidx].decision);
      var j := SendDecideSkolemization(c, v, abortMsg);
      InvImpliesLeaderTallyReflectsPreferences(c, v);
      var rogue :| rogue in v.History(j).coordinator[0].noVotes.s;
      // Need to show rogue is a valid participant id
      var _, voteMsg := ReceiveVoteNoStepSkolemization(c, v, j, 0, rogue);
    }
  }
}

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables, i: int)
  requires RegularInvs(c, v)
  requires v.ValidHistoryIdx(i)
  requires |v.History(i).GetCoordinator(c).yesVotes.s| == |c.participants|
  ensures forall id :: 0 <= id < |c.participants| <==> id in v.History(i).GetCoordinator(c).yesVotes.s
{
  var l := v.History(i).GetCoordinator(c);
  forall id | id in v.History(i).GetCoordinator(c).yesVotes.s
  ensures 0 <= id < |c.participants| {
    reveal_ValidHistory();
    var j, msg := ReceiveVoteYesStepSkolemization(c, v, i, 0, id);  // witness
  }

  forall id | 0 <= id < |c.participants| ensures id in l.yesVotes.s {
    if id !in l.yesVotes.s {
      SetLemma(l.yesVotes.s, id, |c.participants|);
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
