include "spec.dfy"

module PaxosMessageInvariants {

import opened Types
import opened MonotonicityLibrary
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations

// Every message in the network has a valid source
ghost predicate ValidMessageSrc(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: 
  match msg 
    case Prepare(bal) => c.ValidLeaderIdx(bal)
    case Promise(_, acc, _) => c.ValidAcceptorIdx(acc)
    case Propose(bal, _) => c.ValidLeaderIdx(bal)
    case Accept(_, acc) => c.ValidAcceptorIdx(acc)
    case Learn(_, _, _) => true
}

// Leader updates its highestHeard and value based on a Promise message carrying that
// ballot and value
ghost predicate LeaderValidHighestHeard(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, b| c.ValidLeaderIdx(idx) && v.leaders[idx].highestHeardBallot == MNSome(b)
  :: (exists prom: Message ::
        && IsPromiseMessage(v, prom)
        && prom.bal == idx
        && prom.vbOpt == Some(VB(v.leaders[idx].Value(), b))
    )
}

ghost predicate AcceptorValidPendingMsg(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx | c.ValidAcceptorIdx(idx) && v.acceptors[idx].pendingPrepare.Some?
  :: Prepare(v.acceptors[idx].pendingPrepare.value.bal) in v.network.sentMsgs
}

// Learner updates its receivedAccepts map based on a Accept message carrying that 
// accepted ValBal pair
ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, vb, acc | 
    && c.ValidLearnerIdx(idx)
    && vb in v.learners[idx].receivedAccepts.m
    && acc in v.learners[idx].receivedAccepts.m[vb]
  ::
    Accept(vb, acc) in v.network.sentMsgs
}

// Message bundle: 7 clauses in total
ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessageSrc(c, v)             // 4
  && AcceptorValidPendingMsg(c, v)
  && LeaderValidHighestHeard(c, v)
  && LearnerValidReceivedAccepts(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  InvNextValidMessageSrc(c, v, v');
}

lemma InvNextValidMessageSrc(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessageSrc(c, v)
  requires Next(c, v, v')
  ensures ValidMessageSrc(c, v)

/***************************************************************************************
*                                        Utils                                         *
***************************************************************************************/

ghost predicate IsPrepareMessage(v: Variables, m: Message) {
  && m.Prepare?
  && m in v.network.sentMsgs
}

ghost predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

ghost predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

ghost predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}
}  // end module PaxosProof

