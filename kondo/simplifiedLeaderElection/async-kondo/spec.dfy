include "distributedSystem.dfy"

module Obligations {
  import opened UtilitiesLibrary
  import opened DistributedSystem

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
    forall h1, h2 
    {:trigger v.Last().IsLeader(c, h2), v.Last().IsLeader(c, h1)}
    {:trigger v.Last().IsLeader(c, h2), c.ValidHostId(h1)}
    {:trigger v.Last().IsLeader(c, h1), c.ValidHostId(h2)}
    {:trigger c.ValidHostId(h2), c.ValidHostId(h1)}
    :: (
      && c.ValidHostId(h1)
      && c.ValidHostId(h2)
      && v.Last().IsLeader(c, h1)
      && v.Last().IsLeader(c, h2)
     ==>
      h1 == h2
    )
  }
}