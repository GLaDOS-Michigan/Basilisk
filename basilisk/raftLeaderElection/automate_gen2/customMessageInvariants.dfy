include "distributedSystem.dfy"
module CustomMessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem

ghost predicate Custom1ReceiveVoteWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, voter: nat, term: nat)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && term == v.History(i).hosts[idx].ms.term
  && voter != c.hosts[idx].idx
  && voter in v.History(i).hosts[idx].ms.acceptors
}

ghost predicate Custom2SendDeclareLemma(c: Constants, v: Variables, i: nat, idx: int, ms: Host.MonotonicTermState)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.hosts|
{
  && v.History(i).hosts[idx].status.Leader?
  && v.History(i).hosts[idx].ms == ms
}

}
