// User level proofs of application invariants

include "spec.dfy"


module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate ValidMessages(c: Constants, v: Variables)
  requires v.WF(c)
{
  && ValidMessages1(c, v)
  && ValidMessages2(c, v)
}

ghost predicate ValidMessages1(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.VoteReq?
  :: c.ValidHostId(msg.candidate)
}

ghost predicate ValidMessages2(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote?
  :: c.ValidHostId(msg.voter)
}

ghost predicate ReceivedVotesValidity(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, voter | c.ValidHostId(idx) && voter in v.hosts[idx].receivedVotes 
  :: Vote(voter, idx) in v.network.sentMsgs
}

ghost predicate VoteMsgImpliesNominee(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote?
  :: v.hosts[msg.voter].nominee == WOSome(msg.candidate)
}

// Protocol bundle: 4 clauses in total
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessages1(c, v)
  && ValidMessages2(c, v)
  && ReceivedVotesValidity(c, v)
  && VoteMsgImpliesNominee(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  assert ValidMessages(c, v');
  assert ReceivedVotesValidity(c, v');
}

}

