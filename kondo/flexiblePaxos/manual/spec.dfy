include "distributedSystem.dfy"

module Obligations {
  import opened DistributedSystem

  // All learners must learn the same value
  ghost predicate Agreement(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2 |
      && c.ValidLearnerIdx(l1)
      && c.ValidLearnerIdx(l2)
      && v.learners[l1].learned.Some?
      && v.learners[l2].learned.Some?
    ::
      v.learners[l1].learned == v.learners[l2].learned
  }

}