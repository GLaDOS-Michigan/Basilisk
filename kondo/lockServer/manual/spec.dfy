include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem


  ghost predicate HoldsLock(c: Constants, v: Variables, idx: int)
    requires c.WF()
    requires v.WF(c)
    requires c.ValidClientIdx(idx)
  {
    v.clients[idx].hasLock
  }

  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
  forall idx1, idx2 | 
    && c.ValidClientIdx(idx1) 
    && c.ValidClientIdx(idx2) 
    && HoldsLock(c, v, idx1)
    && HoldsLock(c, v, idx2)
    :: idx1 == idx2
  }
}
