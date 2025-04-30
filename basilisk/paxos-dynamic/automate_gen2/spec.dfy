include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem

  // All learners must learn the same value
  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2 
    {:trigger v.Last().hosts[l1].learned == v.Last().hosts[l2].learned}
    |
      && c.ValidHostIdx(l1)
      && c.ValidHostIdx(l2)
      && v.Last().hosts[l1].learned.Some?
      && v.Last().hosts[l2].learned.Some?
    ::
      v.Last().hosts[l1].learned == v.Last().hosts[l2].learned
  }
}
