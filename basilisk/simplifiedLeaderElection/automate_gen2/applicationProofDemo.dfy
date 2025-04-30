include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module ProofDraft {
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
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  SafetyProof(c, v');
}

/***************************************************************************************
*                                    Helper Lemmas                                     *
***************************************************************************************/

// BEGIN SAFETY PROOF

lemma RegInvsYieldIsLeaderImpliesHasQuorum(c: Constants, v: Variables) 
  requires RegularInvs(c, v)
  ensures forall h: nat | c.ValidHostId(h) && v.Last().IsLeader(c, h) :: 
          SetIsQuorum(c.hosts[h].clusterSize, v.Last().hosts[h].receivedVotes.Value())
{
  forall h: nat | c.ValidHostId(h) && v.Last().IsLeader(c, h)
  ensures SetIsQuorum(c.hosts[h].clusterSize, v.Last().hosts[h].receivedVotes.Value()) {
    reveal_ValidHistory();
    var j, step, msgOps := NextVictoryStepStepSkolemization(c, v, |v.history|-1, h, true);
    SetContainmentCardinality(v.History(j).hosts[h].receivedVotes.Value(), v.Last().hosts[h].receivedVotes.Value());
  }
}

lemma RegInvsYieldReceivedVotesValid(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  ensures forall h: nat | c.ValidHostId(h) :: 
          v.Last().hosts[h].receivedVotes.IsSubsetOf(set x: int | 0 <= x < |c.hosts|)
{
  forall h : nat | c.ValidHostId(h) 
  ensures v.Last().hosts[h].receivedVotes.IsSubsetOf(set x: int | 0 <= x < |c.hosts|) {
    forall voter | v.Last().hosts[h].receivedVotes.Contains(voter)
    ensures voter in (set x | 0 <= x < |c.hosts|) {
      reveal_ValidHistory();
      var _, _ := ReceiveVoteStepSkolemization(c, v, |v.history|-1, h, voter);
    }
    MonotonicSetContainmentLemma(v.Last().hosts[h].receivedVotes, set x: int | 0 <= x < |c.hosts|);
  }
}

lemma SafetyProof(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  ensures Safety(c, v)
{
  RegInvsYieldReceivedVotesValid(c, v);
  if !Safety(c, v) {
    ghost var l1: nat :| c.ValidHostId(l1) && v.Last().IsLeader(c, l1);
    ghost var l2: nat :| c.ValidHostId(l2) && v.Last().IsLeader(c, l2) && l2 != l1;
    SetComprehensionSize(|c.hosts|);
    ghost var rv1, rv2 := v.Last().hosts[l1].receivedVotes.Value(), v.Last().hosts[l2].receivedVotes.Value();
    RegInvsYieldIsLeaderImpliesHasQuorum(c, v);
    ghost var rogueId := QuorumIntersection((set x: int | 0 <= x < |c.hosts|), rv1, rv2);
    assert v.Last().hosts[rogueId].nominee == WOSome(l1) && v.Last().hosts[rogueId].nominee == WOSome(l2) by {
      // witnesses
      reveal_ValidHistory();
      var j1, msg1 := ReceiveVoteStepSkolemization(c, v, |v.history|-1, l1, rogueId);
      var j2, msg2 := ReceiveVoteStepSkolemization(c, v, |v.history|-1, l2, rogueId);
      // assert false;
    }
  }
}

// END SAFETY PROOF

} // end module ProofDraft
