include "system.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened System

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall idx1, idx2 | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2)
    && Host.HostOwnsUniqueKey(c.hosts[idx1], v.hosts[idx1], 0)
    && Host.HostOwnsUniqueKey(c.hosts[idx2], v.hosts[idx2], 0)
    :: idx1 == idx2
  }

  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/

  lemma SuccessorPredecessorRelation(n: int, idx: nat) 
    requires 0 < n
    requires idx < n
    ensures Predecessor(n, Successor(n, idx)) == idx
    ensures Successor(n, Predecessor(n, idx)) == idx
  {}

}