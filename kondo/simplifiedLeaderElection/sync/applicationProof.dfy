include "spec.dfy"

module ToyLeaderElectionProof {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened System
import opened Obligations

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Application Invariant: Host having a vote implies voter nominated that host
ghost predicate HasVoteImpliesVoterNominates(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall nominee: nat, voter: nat | 
    && c.ValidHostId(nominee)
    && c.ValidHostId(voter)
    && v.hosts[nominee].HasVoteFrom(voter)
  ::
    v.hosts[voter].Nominates(nominee)
}

ghost predicate ReceivedVotesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall h: nat | c.ValidHostId(h)
  :: v.hosts[h].receivedVotes <= (set x | 0 <= x < |c.hosts|)
}

ghost predicate IsLeaderImpliesHasQuorum(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall h: nat | c.ValidHostId(h) && v.IsLeader(c, h)
  :: SetIsQuorum(c.hosts[h].clusterSize, v.hosts[h].receivedVotes)
}

// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && ReceivedVotesValid(c, v)
  && IsLeaderImpliesHasQuorum(c, v)  // this says that the set size doesn't shrink
  && HasVoteImpliesVoterNominates(c, v)
}

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
  InvNextReceivedVotesValid(c, v, v');
  InvNextIsLeaderImpliesHasQuorum(c, v, v');
  InvNextHasVoteImpliesVoterNominates(c, v, v');
  SafetyProof(c, v');
}


/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

lemma InvNextReceivedVotesValid(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ReceivedVotesValid(c, v')
{}

lemma InvNextIsLeaderImpliesHasQuorum(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires ReceivedVotesValid(c, v')
  ensures IsLeaderImpliesHasQuorum(c, v')
{}

lemma InvNextHasVoteImpliesVoterNominates(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures HasVoteImpliesVoterNominates(c, v')
{}

lemma SafetyProof(c: Constants, v: Variables)
  requires v.WF(c)
  requires ApplicationInv(c, v)
  ensures Safety(c, v)
{
  /* Proof by contradiction: Assume two leaders were elected in v', L1 and L2.
  * Then by quorum intersection, there is a common rogueId in both L1.receivedVotes and
  * L2.receivedVotes. This violates HasVoteImpliesVoterNominates
  */
  if !Safety(c, v) {
    var l1: nat :| c.ValidHostId(l1) && v.IsLeader(c, l1);
    var l2: nat :| c.ValidHostId(l2) && v.IsLeader(c, l2) && l2 != l1;
    var allHosts := (set x | 0 <= x < |c.hosts|);
    SetComprehensionSize(|c.hosts|);

    var rv1, rv2 :=  v.hosts[l1].receivedVotes, v.hosts[l2].receivedVotes;
    var rogueId := QuorumIntersection(allHosts, rv1, rv2);  // witness

    assert v.hosts[rogueId].nominee == WOSome(l1);  // trigger
    assert v.hosts[rogueId].nominee == WOSome(l2);  // trigger
    assert false;
  }
}


// END SAFETY PROOF

} // end module ToyLeaderElectionProof