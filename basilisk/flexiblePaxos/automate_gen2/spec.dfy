include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem

  // All learners must learn the same value
  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2 
    {:trigger v.Last().learners[l1].learned == v.Last().learners[l2].learned}
    |
      && c.ValidLearnerIdx(l1)
      && c.ValidLearnerIdx(l2)
      && v.Last().learners[l1].learned.Some?
      && v.Last().learners[l2].learned.Some?
    ::
      v.Last().learners[l1].learned == v.Last().learners[l2].learned
  }
}
