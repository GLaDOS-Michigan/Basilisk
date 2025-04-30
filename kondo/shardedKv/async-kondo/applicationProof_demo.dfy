/// This file is auto-generated from KondoPrototypes/shardedKv/centralized/applicationProof.dfy
/// Generated 04/02/2024 16:58 Pacific Standard Time

/// This file is then manually modified to complete the proof

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

ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  true
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
  InvNextSafety(c, v, v');
}


/***************************************************************************************
*                                   InvNext Proofs                                     *
***************************************************************************************/

// modified: 7 lines
// Note that the proof is also complete by deleting this lemma
lemma InvNextSafety(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Safety(c, v')
{
  OwnershipInvInductive(c, v, v');
}


lemma AtMostOwnerPerKeyImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneOwnerPerKeyHost(c, v)
  ensures Safety(c, v)
{
  forall idx1, idx2, k: UniqueKey |
    && 0 <= idx1 < |c.hosts|
    && 0 <= idx2 < |c.hosts|
    && Host.HostOwnsUniqueKey(c.hosts[idx1], v.Last().hosts[idx1], k)
    && Host.HostOwnsUniqueKey(c.hosts[idx2], v.Last().hosts[idx2], k)
  ensures idx1 == idx2
  {
    assert Host.HostOwnsUniqueKey(c.hosts[idx1], v.Last().hosts[idx1], k);  // trigger
  }
}


} // end module ProofDraft
