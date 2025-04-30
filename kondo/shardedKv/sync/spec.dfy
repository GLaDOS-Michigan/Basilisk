include "system.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened System

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
    forall idx1, idx2, k: UniqueKey | 
      && c.ValidIdx(idx1)
      && c.ValidIdx(idx2)
      && Host.HostOwnsUniqueKey(c.hosts[idx1], v.hosts[idx1], k)
      && Host.HostOwnsUniqueKey(c.hosts[idx2], v.hosts[idx2], k)
      :: idx1 == idx2
  }
}