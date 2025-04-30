include "distributedSystem.dfy"

module Obligations {
  import opened UtilitiesLibrary
  import opened DistributedSystem

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
    forall h1, h2 | 
      && c.ValidHostId(h1)
      && c.ValidHostId(h2)
      && v.IsLeader(c, h1)
      && v.IsLeader(c, h2)
    ::
      h1 == h2
  }
}