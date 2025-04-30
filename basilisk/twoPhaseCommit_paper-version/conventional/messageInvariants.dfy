include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened Obligations

// Send Invariant
// All Vote have a valid participant HostId as src
ghost predicate VoteValidSrc(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote? 
  :: c.ValidParticipantId(msg.src)
}

// Send Invariant
// Vote reflects the preference of the voter 
// Note that "0 <= msg.src < |c.hosts|-1" is prereq of GetParticipantPreference
ghost predicate VoteAgreeWithVoter(c: Constants, v: Variables)
  requires v.WF(c)
  requires VoteValidSrc(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote? 
  :: GetParticipantPreference(c, msg.src) == msg.v
}

// Send Invariant
// Decides should reflect the decision of the leader
// Note that this hinges on fact that leader does not equivocate
ghost predicate DecisionMsgsAgreeWithLeader(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs && msg.Decide? 
  :: v.GetCoordinator(c).decision.Some? && msg.decision == v.GetCoordinator(c).decision.value
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && VoteValidSrc(c, v)
  && VoteAgreeWithVoter(c, v)
  && DecisionMsgsAgreeWithLeader(c, v)
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
}

