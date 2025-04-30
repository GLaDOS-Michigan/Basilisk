include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

ghost predicate IsLeader(c: Constants, h: Hosts, idx: nat) 
  requires h.WF(c)
  requires c.ValidIdx(idx)
{
  h.hosts[idx].highestHeard == c.hosts[idx].hostId
}

ghost predicate Safety(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx1, idx2 | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && IsLeader(c, v.Last(), idx1)
    && IsLeader(c, v.Last(), idx2)
    :: idx1 == idx2
}
}

