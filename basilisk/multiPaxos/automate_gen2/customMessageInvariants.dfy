include "distributedSystem.dfy"

module CustomMessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate Custom1ReceivePromiseWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Ballot, a2: HostId)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && a1 == v.History(i).hosts[idx].ls.currBal
  && a2 in v.History(i).hosts[idx].ls.promises
}

ghost predicate Custom2ReceivePromiseWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Ballot, a2: Value, a3: Ballot, slot: nat)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && c.ValidSlot(slot)
  && a1 == v.History(i).hosts[idx].ls.currBal
  && a2 == v.History(i).hosts[idx].ls.logHighestHeardValues[slot].v
  && v.History(i).hosts[idx].ls.logHighestHeardValues[slot].ob.Some?
  && a3 == v.History(i).hosts[idx].ls.logHighestHeardValues[slot].ob.value
}
}
