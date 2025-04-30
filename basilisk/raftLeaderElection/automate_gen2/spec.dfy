include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem

  // All learners must learn the same value
  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2 
    |
      && c.ValidHostIdx(l1)
      && c.ValidHostIdx(l2)
      && v.Last().hosts[l1].status.Leader?
      && v.Last().hosts[l2].status.Leader?
      && l1 != l2
    ::
      v.Last().hosts[l1].ms.term != v.Last().hosts[l2].ms.term
  }
}
