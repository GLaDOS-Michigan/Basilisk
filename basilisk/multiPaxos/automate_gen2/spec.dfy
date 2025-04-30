include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem

  // All learners must learn the same value
  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2, slot
    {:trigger v.Last().hosts[l1].logLearned[slot] == v.Last().hosts[l2].logLearned[slot]}
    |
      && c.ValidHostIdx(l1)
      && c.ValidHostIdx(l2)
      && c.ValidSlot(slot)
      && v.Last().hosts[l1].logLearned[slot].Some?
      && v.Last().hosts[l2].logLearned[slot].Some?
    ::
      v.Last().hosts[l1].logLearned[slot] == v.Last().hosts[l2].logLearned[slot]
  }
}
