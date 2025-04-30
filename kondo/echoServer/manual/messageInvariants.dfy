include "spec.dfy"

module MessageInvariants {

import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// Every request message in the network has a proper source
ghost predicate RequestMsgsValidSource(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: c.ValidClientIdx(req.r.clientId)
}

// Every request message in the network comes from the source's request set
// Property of Send
ghost predicate RequestMsgsValid(c: Constants, v: Variables)
  requires v.WF(c)
  requires RequestMsgsValidSource(c, v)
{
  forall req | req in v.network.sentMsgs && req.RequestMsg?
  :: req.r.reqId in v.clients[req.r.clientId].requests.s
}

// The server's current request must have come from the network
// Property of Receive
ghost predicate ServerCurrentRequestValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  v.GetServer(c).currentRequest.Some?
  ==> RequestMsg(v.GetServer(c).currentRequest.value) in v.network.sentMsgs
}

// Every client's collected responses came from the network.
// Property of Receive
ghost predicate ClientResponsesValid(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx:nat, respId | c.ValidClientIdx(idx) && respId in v.clients[idx].responses
  :: ResponseMsg(Req(idx, respId)) in v.network.sentMsgs
}

// Message bundle: 4 clauses in total
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && RequestMsgsValidSource(c, v)
  && RequestMsgsValid(c, v)
  && ServerCurrentRequestValid(c, v)
  && ClientResponsesValid(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{}

}  // end module MessageInvariants

