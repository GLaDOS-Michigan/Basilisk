// include "messageInvariantsAutogen.dfy"
include "distributedSystem.dfy"
module CustomMessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
// import opened MessageInvariants

ghost predicate Custom1ReceivePromise1ReceivePromise2WitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Ballot, a2: HostId)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && a1 == v.History(i).hosts[idx].ls.currBal
  && a2 in v.History(i).hosts[idx].ls.promises
}

ghost predicate Custom2ReceivePromise1ReceivePromise2WitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Ballot, a2: Value, a3: Ballot)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && a1 == v.History(i).hosts[idx].ls.currBal
  && a2 == v.History(i).hosts[idx].ls.value
  && v.History(i).hosts[idx].ls.highestHeardBallot.Some?
  && a3 == v.History(i).hosts[idx].ls.highestHeardBallot.value
}

}
