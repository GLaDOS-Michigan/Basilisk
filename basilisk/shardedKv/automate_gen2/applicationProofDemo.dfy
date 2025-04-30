include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"
include "ownershipInvariantsAutogen.dfy"

module ProofDraft {
  import opened MonotonicityLibrary
  import opened DistributedSystem
  import opened MonotonicityInvariants
  import opened MessageInvariants
  import opened Obligations
  import opened OwnershipInvariants

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && OwnershipInv(c, v)
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
{
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  OwnershipInvInductive(c, v, v');
}


/***************************************************************************************
*                                   InvNext Proofs                                     *
***************************************************************************************/

// BEGIN SAFETY PROOF
// END SAFETY PROOF

} // end module ProofDraft
