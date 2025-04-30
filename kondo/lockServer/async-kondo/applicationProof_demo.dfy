/// This file is auto-generated from KondoPrototypes/lockServer/centralized/applicationProof.dfy
/// Generated 04/02/2024 16:54 Pacific Standard Time

/// It is then manually modified to complete the proof

include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"
include "ownershipInvariantsAutogen.dfy"

module ProofDraft {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary
  import opened DistributedSystem
  import opened MonotonicityInvariants
  import opened MessageInvariants
  import opened Obligations
  import opened OwnershipInvariants

ghost predicate ServerOwnsLockImpliesNoClientsOwnsLock(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall i :: v.ValidHistoryIdx(i) ==> (
    v.History(i).server[0].hasLock ==>
      forall id: int
 {:trigger v.History(i).clients[id]} {:trigger c.ValidClientIdx(id), v.ValidHistoryIdx(i)}
 | c.ValidClientIdx(id) :: 
        !v.History(i).clients[id].hasLock
  )
}

ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && ServerOwnsLockImpliesNoClientsOwnsLock(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && OwnershipInv(c, v)
  && ProtocolInv(c, v)
  && Safety(c, v)
}

/***************************************************************************************
*                                    Obligations                                       *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMonotonicityInv(c, v);
  InitImpliesMessageInv(c, v);
  InitImpliesOwnershipInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  OwnershipInvInductive(c, v, v');
  AtMostOwnerPerKeyImpliesSafety(c, v');
  InvNextServerOwnsLockImpliesNoClientsOwnsLock(c, v, v');
}


/***************************************************************************************
*                                   InvNext Proofs                                     *
***************************************************************************************/


// modified: 15 lines
// Note that an alternative proof is to remove this invariant altogether, as Safety is
// also implied by OwnershipInv
lemma InvNextServerOwnsLockImpliesNoClientsOwnsLock(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerOwnsLockImpliesNoClientsOwnsLock(c, v')
{
  forall i | v'.ValidHistoryIdx(i) && ServerHost.HostOwnsUniqueKey(c.server[0], v'.History(i).server[0], 0)
  ensures forall id: int | c.ValidClientIdx(id) :: !ClientHost.HostOwnsUniqueKey(c.clients[id], v'.History(i).clients[id], 0)
  {
    VariableNextProperties(c, v, v');
    OwnershipInvInductive(c, v, v');
    if i == |v'.history| - 1 {
      assert !NoServerHostOwnsKey(c, v', 0);  // trigger
    }
  }
}

lemma AtMostOwnerPerKeyImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneOwnerPerKeyClientHost(c, v)
  ensures Safety(c, v)
  requires AtMostOneOwnerPerKeyServerHost(c, v)
  ensures Safety(c, v)
{
  forall idx1, idx2, k: UniqueKey |
    && 0 <= idx1 < |c.clients|
    && 0 <= idx2 < |c.clients|
    && ClientHost.HostOwnsUniqueKey(c.clients[idx1], v.Last().clients[idx1], k)
    && ClientHost.HostOwnsUniqueKey(c.clients[idx2], v.Last().clients[idx2], k)
  ensures idx1 == idx2
  {
    assert ClientHost.HostOwnsUniqueKey(c.clients[idx1], v.Last().clients[idx1], k);  // trigger
  }
  forall idx1, idx2, k: UniqueKey |
    && 0 <= idx1 < |c.server|
    && 0 <= idx2 < |c.server|
    && ServerHost.HostOwnsUniqueKey(c.server[idx1], v.Last().server[idx1], k)
    && ServerHost.HostOwnsUniqueKey(c.server[idx2], v.Last().server[idx2], k)
  ensures idx1 == idx2
  {
    assert ServerHost.HostOwnsUniqueKey(c.server[idx1], v.Last().server[idx1], k);  // trigger
  }
}


} // end module ProofDraft
