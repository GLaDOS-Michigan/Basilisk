include "messageInvariants.dfy"

module Proof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened MessageInvariants
  import opened Obligations

ghost predicate LeaderVotesValid(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall hostId: int| hostId in v.GetCoordinator(c).yesVotes.s 
  :: 
  0 <= hostId < |c.participants|
}

ghost predicate LeaderTallyReflectsPreferences(c: Constants, v: Variables)
  requires v.WF(c)
  requires LeaderVotesValid(c, v)
{
  forall hostId | hostId in v.GetCoordinator(c).yesVotes.s
  :: GetParticipantPreference(c, hostId) == Yes
}

ghost predicate CommitImpliesYesVotesFull(c: Constants, v: Variables)
  requires v.WF(c)
{
  CoordinatorDecidedCommit(c, v)
  ==>
  |v.GetCoordinator(c).yesVotes.s| >= |c.participants|
}

ghost predicate ParticipantDecisionReflectLeader(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall id | c.ValidParticipantId(id) && ParticipantDecidedCommit(c, v, id) 
  :: CoordinatorDecidedCommit(c, v)
}


ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LeaderVotesValid(c, v)
  && LeaderTallyReflectsPreferences(c, v)
  && CommitImpliesYesVotesFull(c, v)
  && ParticipantDecisionReflectLeader(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ApplicationInv(c, v)
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
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
  InvNextLeaderVotesValid(c, v, v');
  InvNextLeaderTallyReflectsPreferences(c, v, v');
  InvNextCommitImpliesYesVotesFull(c, v, v');
  InvNextParticipantDecisionReflectLeader(c, v, v');
  AC3Proof(c, v');
}


/***************************************************************************************
*                                   InvNext Proofs                                     *
***************************************************************************************/

lemma InvNextLeaderVotesValid(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderVotesValid(c, v')
{}

lemma InvNextLeaderTallyReflectsPreferences(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderVotesValid(c, v')
  ensures LeaderTallyReflectsPreferences(c, v')
{}

lemma InvNextCommitImpliesYesVotesFull(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures CommitImpliesYesVotesFull(c, v')
{
  if CoordinatorDecidedCommit(c, v') {
    var dsStep :| NextStep(c, v, v', dsStep);
    if dsStep.CoordinatorStep? {
      if !CoordinatorDecidedCommit(c, v) {
        // triggers
        assert CoordinatorDecidedCommit(c, v');
        assert v.GetCoordinator(c).yesVotes.s == v'.GetCoordinator(c).yesVotes.s;
        assert |v.GetCoordinator(c).yesVotes.s| == |v'.GetCoordinator(c).yesVotes.s|;
        assert |v.GetCoordinator(c).yesVotes.s| == |c.participants|;
        assert |v'.GetCoordinator(c).yesVotes.s| >= |c.participants|;
      } else {
        SetContainmentCardinality(v.GetCoordinator(c).yesVotes.s, v'.GetCoordinator(c).yesVotes.s);
      }
    } else {
      assert CommitImpliesYesVotesFull(c, v');  // trigger
    }
  }
}

lemma InvNextParticipantDecisionReflectLeader(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ParticipantDecisionReflectLeader(c, v')
{}

lemma AC3Proof(c: Constants, v: Variables)
  requires MessageInv(c, v)
  requires ApplicationInv(c, v)
  ensures SafetyAC3(c, v)
{
  forall pidx: nat | c.ValidParticipantId(pidx) && ParticipantDecidedCommit(c, v, pidx)
  ensures AllPreferYes(c) {
    if !AllPreferYes(c) {
      var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
      YesVotesContainsAllParticipantsWhenFull(c, v);
      assert noVoter in v.GetCoordinator(c).yesVotes.s;  // trigger
    }
  }
}



/***************************************************************************************
*                                    Helper Lemmas                                     *
***************************************************************************************/

lemma YesVotesContainsAllParticipantsWhenFull(c: Constants, v: Variables)
  requires v.WF(c)
  requires ApplicationInv(c, v)
  requires |v.GetCoordinator(c).yesVotes.s| >= |c.participants|
  ensures forall id: int
 
 | 0 <= id < |c.participants| :: id in v.GetCoordinator(c).yesVotes.s
  decreases c, v
{
  ghost var l := v.GetCoordinator(c);
  forall id: int

 | 0 <= id < |c.participants|
    ensures id in l.yesVotes.s
  {
    if id !in l.yesVotes.s {
      SetLemma(l.yesVotes.s, id, |c.participants|);
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
