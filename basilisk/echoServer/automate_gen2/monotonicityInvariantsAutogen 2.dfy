/// This file is auto-generated from /Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/basilisk/echoServer/automate_gen2/distributedSystem.dfy
/// Generated 03/07/2025 21:42 Pacific Standard Time
include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate ClientHostRequestsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.clients|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).clients[idx].requests.SatisfiesMonotonic(v.History(i).clients[idx].requests)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ClientHostRequestsMonotonic(c, v)
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
