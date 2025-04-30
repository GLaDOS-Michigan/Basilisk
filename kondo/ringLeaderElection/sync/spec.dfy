include "system.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened System

ghost predicate IsLeader(c: Constants, v: Variables, idx: nat) 
    requires v.WF(c)
    requires c.ValidIdx(idx)
{
    v.hosts[idx].highestHeard == c.hosts[idx].hostId
}

ghost predicate Safety(c: Constants, v: Variables) 
    requires v.WF(c)
{
    forall idx1, idx2 | 
        && c.ValidIdx(idx1) 
        && c.ValidIdx(idx2) 
        && IsLeader(c, v, idx1)
        && IsLeader(c, v, idx2)
        :: idx1 == idx2
}
}
