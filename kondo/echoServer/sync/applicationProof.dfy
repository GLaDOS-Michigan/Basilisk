include "spec.dfy"

module ClientServerProof {
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations
  

/***************************************************************************************
*                                Application Invariants                                *
***************************************************************************************/

ghost predicate ServerRequestsValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  && v.GetServer(c).currentRequest.Some?
  && c.ValidClientIdx(v.GetServer(c).currentRequest.value.clientId)
  ==> 
  && var req := v.GetServer(c).currentRequest.value;
  && req.reqId in v.clients[req.clientId].requests.s
}

ghost predicate ApplicationInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  ServerRequestsValid(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ApplicationInv(c, v)
  && Safety(c, v)
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
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{}

// BEGIN SAFETY PROOF
// END SAFETY PROOF

}  // end module ClientServerProof

