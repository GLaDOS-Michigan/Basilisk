/// This file is auto-generated from /Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/basilisk/distributedLock/automate_gen2/distributedSystem.dfy
/// Generated 11/23/2024 20:17 Pacific Standard Time
include "spec.dfy"

module OwnershipInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

/***************************************************************************************
*                                     Definitions                                       *
***************************************************************************************/

ghost predicate {:trigger KeyInFlightByMessage} UniqueKeyInFlight(c: Constants, v: Variables, k: UniqueKey)
requires v.WF(c)
{
  exists msg :: KeyInFlightByMessage(c, v, msg, k)
}

// Disjunction for each host type
ghost predicate {:trigger UniqueKeyInFlight} KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: UniqueKey)
   requires v.WF(c)
{
  && msg in v.network.sentMsgs
  && (      || (0 <= msg.Dst() < |c.hosts| &&
         Host.UniqueKeyInFlightForHost(c.hosts[msg.Dst()], v.Last().hosts[msg.Dst()], k, msg)
       )
     )
}

// One for each host type
ghost predicate NoHostOwnsKey(c: Constants, v: Variables, k: UniqueKey)
  requires v.WF(c)
{
  forall idx | 0 <= idx < |c.hosts|
  ::
  !Host.HostOwnsUniqueKey(c.hosts[idx], v.Last().hosts[idx], k)
}

// Conjunction of corresponding assertions for each host type
ghost predicate {:trigger KeyInFlightByMessage, UniqueKeyInFlight} NoHostOwnsKeyMain(c: Constants, v: Variables, k: UniqueKey)
  requires v.WF(c)
{
  && NoHostOwnsKey(c, v, k)
}

/***************************************************************************************
*                                     Invariants                                       *
***************************************************************************************/


ghost predicate AtMostOneInFlightMessagePerKey(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k)
  :: m1 == m2
}


ghost predicate {:trigger Host.HostOwnsUniqueKey}
HostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall k | !NoHostOwnsKeyMain(c, v, k)
  ::
  !UniqueKeyInFlight(c, v, k)
}

// One for each host type
ghost predicate AtMostOneOwnerPerKeyHost(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall h1, h2, k |
    && 0 <= h1 < |c.hosts| && 0 <= h2 < |c.hosts|
    && Host.HostOwnsUniqueKey(c.hosts[h1], v.Last().hosts[h1], k)
    && Host.HostOwnsUniqueKey(c.hosts[h2], v.Last().hosts[h2], k)
  ::
    h1 == h2
}

ghost predicate OwnershipInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && AtMostOneInFlightMessagePerKey(c, v)
  && HostOwnsKeyImpliesNotInFlight(c, v)
  && AtMostOneOwnerPerKeyHost(c, v)
}

lemma InitImpliesOwnershipInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures OwnershipInv(c, v)
{}

lemma OwnershipInvInductive(c: Constants, v: Variables, v': Variables)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures OwnershipInv(c, v')
{
  InvNextAtMostOneInFlightMessagePerKey(c, v, v');
  InvNextHostOwnsKeyImpliesNotInFlight(c, v, v');
  InvNextAtMostOneOwnerPerKeyHost(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/

lemma InvNextAtMostOneInFlightMessagePerKey(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneInFlightMessagePerKey(c, v')
{
  forall k, m1, m2 | KeyInFlightByMessage(c, v', m1, k) && KeyInFlightByMessage(c, v', m2, k)
  ensures m1 == m2
  {
    if m1 != m2 {
      if KeyInFlightByMessage(c, v, m1, k) {
        InvNextAtMostOneInFlightHelper(c, v, v', m1, m2, k);
      } else {
        InvNextAtMostOneInFlightHelper(c, v, v', m2, m1, k);
      }
     }
  }
}

lemma InvNextAtMostOneInFlightHelper(c: Constants, v: Variables, v': Variables, m1: Message, m2: Message, k: UniqueKey)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  // input constraints
  requires m1 != m2
  requires KeyInFlightByMessage(c, v, m1, k)
  requires !KeyInFlightByMessage(c, v, m2, k)
  // postcondition
  ensures !KeyInFlightByMessage(c, v', m2, k)
{
  assert UniqueKeyInFlight(c, v, k);
}

lemma InvNextHostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsKeyImpliesNotInFlight(c, v')
{
  forall k | !NoHostOwnsKeyMain(c, v', k)
  ensures !UniqueKeyInFlight(c, v', k)
  {
    if UniqueKeyInFlight(c, v', k) {
      var msg :| KeyInFlightByMessage(c, v', msg , k);
      if msg in v.network.sentMsgs {
        assert KeyInFlightByMessage(c, v, msg, k);
        assert NoHostOwnsKeyMain(c, v, k);
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        assert dsStep.msgOps.recv.value == msg by {
          if dsStep.msgOps.recv.value != msg {
            var m' := dsStep.msgOps.recv.value;
            assert !KeyInFlightByMessage(c, v, m', k);
          }
        }
      } else {
        assert !(NoHostOwnsKeyMain(c, v, k));
      }
    }
  }
}

// One for each host type
lemma InvNextAtMostOneOwnerPerKeyHost(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneOwnerPerKeyHost(c, v')
{
  forall h1, h2, k |
    && 0 <= h1 < |c.hosts| && 0 <= h2 < |c.hosts|
    && Host.HostOwnsUniqueKey(c.hosts[h1], v'.Last().hosts[h1], k)
    && Host.HostOwnsUniqueKey(c.hosts[h2], v'.Last().hosts[h2], k)
  ensures
    h1 == h2
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    if h1 != h2 {
      assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k); 
      assert UniqueKeyInFlight(c, v, k);
    }
  }
}

}  // end OwnershipInvariants module
