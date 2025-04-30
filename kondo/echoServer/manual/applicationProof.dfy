include "spec.dfy"
include "messageInvariants.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants
  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

// Protocol bundle: 1 clause in total
ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
  requires MessageInv(c, v)
{
  ResponseCorrespondToRequest(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && ProtocolInv(c, v)
  && Safety(c, v)
}

ghost predicate ResponseCorrespondToRequest(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall resp | resp in v.network.sentMsgs && resp.ResponseMsg?
  :: RequestMsg(resp.r) in v.network.sentMsgs
}

/***************************************************************************************
*                                        Proof                                         *
***************************************************************************************/

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MessageInvInductive(c, v, v');
}
}  // end module ClientServerProof

