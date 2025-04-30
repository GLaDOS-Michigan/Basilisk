include "spec.dfy"

module ShardedKVProof {
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations


// Application bundle
ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && true
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ApplicationInv(c, v)
  && Safety(c, v)
}


/***************************************************************************************
*                                Top-level Obligations                                 *
***************************************************************************************/


lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  InvNextSafety(c, v, v');
}


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

// BEGIN SAFETY PROOF

lemma InvNextSafety(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Safety(c, v')
{
  forall idx1, idx2, k: UniqueKey | 
    && c.ValidIdx(idx1) 
    && c.ValidIdx(idx2) 
    && Host.HostOwnsUniqueKey(c.hosts[idx1], v'.hosts[idx1], k)
    && Host.HostOwnsUniqueKey(c.hosts[idx2], v'.hosts[idx2], k)
  ensures 
    idx1 == idx2
  {
    var sysStep :| NextStep(c, v, v', sysStep);
    if sysStep.Transfer? {
      if idx1 != idx2 && k == sysStep.transmit.m.key {
        var sender, receiver := sysStep.sender, sysStep.receiver;
        if idx1 == sender && idx2 == receiver {
          assert false;
        } else if idx1 == sysStep.receiver && idx2 == sysStep.sender {
          assert false;
        } else {
          assert idx1 == idx2;
        }
      }
    }
  }
}

// END SAFETY PROOF

} // end module ToylockProof