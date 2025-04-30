include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate CoordinatorHostYesVotesMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.coordinator|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).coordinator[idx].yesVotes.SatisfiesMonotonic(v.History(i).coordinator[idx].yesVotes)
}

ghost predicate CoordinatorHostNoVotesMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.coordinator|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).coordinator[idx].noVotes.SatisfiesMonotonic(v.History(i).coordinator[idx].noVotes)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && CoordinatorHostYesVotesMonotonic(c, v)
  && CoordinatorHostNoVotesMonotonic(c, v)
}

// Base obligation
lemma InitImpliesMonotonicityInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MonotonicityInv(c, v)
{
}

// Inductive obligation
lemma MonotonicityInvInductive(c: Constants, v: Variables, v': Variables)
  requires MonotonicityInv(c, v)
  requires Next(c, v, v')
  ensures MonotonicityInv(c, v')
{
  VariableNextProperties(c, v, v');
}

} // end module MonotonicityInvariants
