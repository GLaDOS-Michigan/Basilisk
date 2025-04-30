include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall idx1, idx2 | 
    && c.ValidClientIdx(idx1) 
    && c.ValidClientIdx(idx2) 
    && ClientHost.HostOwnsUniqueKey(c.clients[idx1], v.Last().clients[idx1], 0)
    && ClientHost.HostOwnsUniqueKey(c.clients[idx2], v.Last().clients[idx2], 0)
    :: idx1 == idx2
  }
}
