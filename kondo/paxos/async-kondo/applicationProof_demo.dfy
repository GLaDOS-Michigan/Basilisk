/// This file is auto-generated from KondoPrototypes/paxos/centralized/applicationProof.dfy
/// Generated 04/02/2024 16:05 Pacific Standard Time

/// This file is then manually modified to complete the proof

include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module Proof {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary
  import opened DistributedSystem
  import opened MonotonicityInvariants
  import opened MessageInvariants
  import opened Obligations

ghost predicate LearnerValidReceivedAccepts(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall lnr: LearnerId, vb: ValBal, e: AcceptorId, i: nat
 {:trigger c.ValidAcceptorIdx(e), v.History(i).learners[lnr].receivedAccepts.m[vb]} {:trigger c.ValidAcceptorIdx(e), vb in v.History(i).learners[lnr].receivedAccepts.m}
 | v.ValidHistoryIdx(i) && c.ValidLearnerIdx(lnr) && vb in v.History(i).learners[lnr].receivedAccepts.m && e in v.History(i).learners[lnr].receivedAccepts.m[vb] :: 
    c.ValidAcceptorIdx(e)
}

ghost predicate LearnedImpliesQuorumOfAccepts(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall lnr: LearnerId, val: Value, i: nat
 {:trigger v.History(i).learners[lnr].HasLearnedValue(val)}
 | v.ValidHistoryIdx(i) && c.ValidLearnerIdx(lnr) && v.History(i).learners[lnr].HasLearnedValue(val) :: 
    exists b: LeaderId
 :: 
      ChosenAtLearner(c, v.History(i), VB(val, b), lnr)
}

ghost predicate LearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall lnr: LearnerId, vb: ValBal, i: nat
 {:trigger vb.v, v.History(i).learners[lnr]} {:trigger vb.v, c.ValidLearnerIdx(lnr), v.ValidHistoryIdx(i)} {:trigger vb.b, v.History(i).learners[lnr]} {:trigger vb.b, c.ValidLearnerIdx(lnr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLearnerIdx(lnr) && vb in v.History(i).learners[lnr].receivedAccepts.m && c.ValidLeaderIdx(vb.b) :: 
    v.History(i).LeaderCanPropose(c, vb.b) &&
    v.History(i).leaders[vb.b].Value() == vb.v
}

ghost predicate LearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall lnr: LearnerId, vb: ValBal, acc: AcceptorId, i: nat
 {:trigger vb.b, v.History(i).acceptors[acc], v.History(i).learners[lnr]} {:trigger vb.b, v.History(i).acceptors[acc], c.ValidLearnerIdx(lnr)} {:trigger vb.b, v.History(i).learners[lnr], c.ValidAcceptorIdx(acc)} {:trigger vb.b, c.ValidAcceptorIdx(acc), c.ValidLearnerIdx(lnr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLearnerIdx(lnr) && c.ValidAcceptorIdx(acc) && vb in v.History(i).learners[lnr].receivedAccepts.m && acc in v.History(i).learners[lnr].receivedAccepts.m[vb] :: 
    v.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b)
}

ghost predicate AcceptorValidPromisedAndAccepted(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall acc: AcceptorId, i: nat
 {:trigger v.History(i).acceptors[acc]} {:trigger c.ValidAcceptorIdx(acc), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidAcceptorIdx(acc) && v.History(i).acceptors[acc].acceptedVB.MVBSome? :: 
    c.ValidLeaderIdx(v.History(i).acceptors[acc].acceptedVB.value.b)
}

ghost predicate AcceptorAcceptedImpliesProposed(c: Constants, v: Variables)
  requires v.WF(c)
  requires AcceptorValidPromisedAndAccepted(c, v)
  decreases c, v
{
  forall acc: AcceptorId, i: nat
 {:trigger v.History(i).acceptors[acc]} {:trigger c.ValidAcceptorIdx(acc), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidAcceptorIdx(acc) && v.History(i).acceptors[acc].acceptedVB.MVBSome? :: 
    ghost var vb: ValBal := v.History(i).acceptors[acc].acceptedVB.value; v.History(i).LeaderCanPropose(c, vb.b) && v.History(i).leaders[vb.b].Value() == vb.v
}

ghost predicate LeaderValidReceivedPromises(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall ldr: int, acc: int, i: nat
 {:trigger c.ValidAcceptorIdx(acc), v.History(i).leaders[ldr]} {:trigger c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLeaderIdx(ldr) && acc in v.History(i).leaders[ldr].ReceivedPromises() :: 
    c.ValidAcceptorIdx(acc)
}

ghost predicate LeaderHighestHeardUpperBound(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall ldr: LeaderId, i: nat
 {:trigger v.History(i).leaders[ldr]} {:trigger c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLeaderIdx(ldr) && v.History(i).leaders[ldr].highestHeardBallot.MNSome? :: 
    v.History(i).leaders[ldr].highestHeardBallot.value < ldr
}

ghost predicate LeaderHearedImpliesProposed(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall ldr: LeaderId, i: nat
 {:trigger v.History(i).leaders[ldr].highestHeardBallot}
 | v.ValidHistoryIdx(i) && c.ValidLeaderIdx(ldr) && v.History(i).leaders[ldr].highestHeardBallot.MNSome? && c.ValidLeaderIdx(v.History(i).leaders[ldr].highestHeardBallot.value) :: 
    ghost var b: nat := v.History(i).leaders[ldr].highestHeardBallot.value; v.History(i).LeaderCanPropose(c, b) && v.History(i).leaders[b].Value() == v.History(i).leaders[ldr].Value()
}

ghost predicate LeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall ldr: LeaderId, acc: AcceptorId, i: nat
 {:trigger v.History(i).acceptors[acc], v.History(i).leaders[ldr]} {:trigger v.History(i).acceptors[acc], c.ValidLeaderIdx(ldr)} {:trigger v.History(i).leaders[ldr], c.ValidAcceptorIdx(acc)} {:trigger c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLeaderIdx(ldr) && c.ValidAcceptorIdx(acc) && acc in v.History(i).leaders[ldr].ReceivedPromises() :: 
    v.History(i).acceptors[acc].HasPromisedAtLeast(ldr)
}

ghost predicate LeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall ldr: int, acc: int, lnr: int, vb: ValBal, i: nat
 {:trigger v.History(i).leaders[ldr], vb.b, v.History(i).learners[lnr], c.ValidAcceptorIdx(acc)} {:trigger v.History(i).leaders[ldr], vb.b, c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc)} {:trigger vb.b, v.History(i).learners[lnr], c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr)} {:trigger vb.b, c.ValidLearnerIdx(lnr), c.ValidAcceptorIdx(acc), c.ValidLeaderIdx(ldr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLeaderIdx(ldr) && c.ValidAcceptorIdx(acc) && c.ValidLearnerIdx(lnr) && vb in v.History(i).learners[lnr].receivedAccepts.m && vb.b < ldr && v.History(i).leaders[ldr].HeardAtMost(vb.b) && acc in v.History(i).leaders[ldr].ReceivedPromises() :: 
    acc !in v.History(i).learners[lnr].receivedAccepts.m[vb]
}

ghost predicate ChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall vb: ValBal, acc: AcceptorId, i: nat
 {:trigger vb.v, v.History(i).acceptors[acc].acceptedVB.value.v} {:trigger vb.b, v.History(i).acceptors[acc].acceptedVB.value.b} {:trigger v.History(i).acceptors[acc], Chosen(c, v.History(i), vb)} {:trigger c.ValidAcceptorIdx(acc), Chosen(c, v.History(i), vb)}
 | v.ValidHistoryIdx(i) && Chosen(c, v.History(i), vb) && c.ValidAcceptorIdx(acc) && v.History(i).acceptors[acc].acceptedVB.MVBSome? && v.History(i).acceptors[acc].acceptedVB.value.b >= vb.b :: 
    v.History(i).acceptors[acc].acceptedVB.value.v == vb.v
}

ghost predicate ChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall vb: ValBal, ldrBal: LeaderId, i: nat
 {:trigger v.History(i).leaders[ldrBal], vb.b} {:trigger v.History(i).leaders[ldrBal], Chosen(c, v.History(i), vb)} {:trigger v.History(i).LeaderCanPropose(c, ldrBal), vb.b} {:trigger v.History(i).LeaderCanPropose(c, ldrBal), Chosen(c, v.History(i), vb)} {:trigger vb.b, c.ValidLeaderIdx(ldrBal), v.ValidHistoryIdx(i)} {:trigger c.ValidLeaderIdx(ldrBal), Chosen(c, v.History(i), vb)}
 | v.ValidHistoryIdx(i) && Chosen(c, v.History(i), vb) && c.ValidLeaderIdx(ldrBal) && vb.b < ldrBal && v.History(i).LeaderCanPropose(c, ldrBal) :: 
    v.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
}

ghost predicate ChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall vb: ValBal, ldrBal: LeaderId, i: nat
 {:trigger vb.v, v.History(i).leaders[ldrBal]} {:trigger vb.v, c.ValidLeaderIdx(ldrBal), v.ValidHistoryIdx(i)} {:trigger vb.b, v.History(i).leaders[ldrBal]} {:trigger vb.b, c.ValidLeaderIdx(ldrBal), v.ValidHistoryIdx(i)} {:trigger v.History(i).leaders[ldrBal], Chosen(c, v.History(i), vb)} {:trigger c.ValidLeaderIdx(ldrBal), Chosen(c, v.History(i), vb)}
 | v.ValidHistoryIdx(i) && Chosen(c, v.History(i), vb) && c.ValidLeaderIdx(ldrBal) && v.History(i).leaders[ldrBal].highestHeardBallot.MNSome? && v.History(i).leaders[ldrBal].highestHeardBallot.value >= vb.b :: 
    v.History(i).leaders[ldrBal].Value() == vb.v
}

ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && LearnerValidReceivedAccepts(c, v)
  && LearnedImpliesQuorumOfAccepts(c, v)
  && LearnerReceivedAcceptImpliesProposed(c, v)
  && LearnerReceivedAcceptImpliesAccepted(c, v)
  && AcceptorValidPromisedAndAccepted(c, v)
  && AcceptorAcceptedImpliesProposed(c, v)
  && LeaderValidReceivedPromises(c, v)
  && LeaderHighestHeardUpperBound(c, v)
  && LeaderHearedImpliesProposed(c, v)
  && LeaderReceivedPromisesImpliesAcceptorState(c, v)
  && LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v)
  && ChosenValImpliesAcceptorOnlyAcceptsVal(c, v)
  && ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  && ChosenValImpliesLeaderOnlyHearsVal(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
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
  InvNextLearnerValidReceivedAccepts(c, v, v');
  InvNextLearnedImpliesQuorumOfAccepts(c, v, v');
  InvNextLearnerReceivedAcceptImpliesProposed(c, v, v');
  InvNextLearnerReceivedAcceptImpliesAccepted(c, v, v');
  InvNextAcceptorValidBundle(c, v, v');
  InvNextLeaderValidReceivedPromises(c, v, v');
  InvNextLeaderHighestHeardUpperBound(c, v, v');
  InvNextLeaderHearedImpliesProposed(c, v, v');
  InvNextLeaderReceivedPromisesImpliesAcceptorState(c, v, v');
  InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c, v, v');
  InvNextChosenImpliesProposingLeaderHearsChosenBallot(c, v, v');
  InvNextChosenValImpliesLeaderOnlyHearsVal(c, v, v');
  InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c, v, v');
  InvImpliesAtMostOneChosenVal(c, v');
  AtMostOneChosenImpliesSafety(c, v');
}


/***************************************************************************************
*                                   InvNext Proofs                                     *
***************************************************************************************/

lemma InvNextLearnerValidReceivedAccepts(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MonotonicityInv(c, v)
  requires MessageInv(c, v)
  requires LearnerValidReceivedAccepts(c, v)
  requires Next(c, v, v')
  ensures LearnerValidReceivedAccepts(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

// modified: 28 lines
lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires ProtocolInv(c, v)
  requires Next(c, v, v')
  ensures LearnedImpliesQuorumOfAccepts(c, v')
{
  forall lnr:LearnerId, val:Value, i |
    && v'.ValidHistoryIdx(i)
    && c.ValidLearnerIdx(lnr)
    && v'.History(i).learners[lnr].HasLearnedValue(val)
  ensures
    exists b: LeaderId :: var vb := VB(val, b); ChosenAtLearner(c, v'.History(i), vb, lnr)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if dsStep.LearnerHostStep? && actor == lnr {
        var lc, l, l' := c.learners[actor], v.Last().learners[actor], v'.Last().learners[actor];
        var step :| LearnerHost.NextStep(lc, l, l', step, msgOps);
        if !step.LearnStep? {
          assert v.History(i-1).learners[lnr].HasLearnedValue(val); // trigger
        }
      }
    }
  }
}


lemma {:timeLimitMultiplier 2} InvNextLearnerReceivedAcceptImpliesProposed(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnerReceivedAcceptImpliesProposed(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLearnerReceivedAcceptImpliesAccepted(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LearnerReceivedAcceptImpliesAccepted(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
  assert LearnerReceivedAcceptImpliesAccepted(c, v');
}

lemma InvNextAcceptorValidBundle(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MonotonicityInv(c, v)
  requires MessageInv(c, v)
  requires AcceptorValidPromisedAndAccepted(c, v)
  requires AcceptorAcceptedImpliesProposed(c, v)
  requires Next(c, v, v')
  ensures AcceptorValidPromisedAndAccepted(c, v')
  ensures AcceptorAcceptedImpliesProposed(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
  assert AcceptorValidPromisedAndAccepted(c, v');
  assert AcceptorAcceptedImpliesProposed(c, v');
}

lemma InvNextLeaderValidReceivedPromises(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderValidReceivedPromises(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderHighestHeardUpperBound(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardUpperBound(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderHearedImpliesProposed(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromisedAndAccepted(c, v')
  requires AcceptorAcceptedImpliesProposed(c, v')
  ensures LeaderHearedImpliesProposed(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

lemma InvNextLeaderReceivedPromisesImpliesAcceptorState(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires MonotonicityInv(c, v)
  requires MessageInv(c, v)
  requires LeaderHearedImpliesProposed(c, v)
  requires LeaderReceivedPromisesImpliesAcceptorState(c, v)
  requires Next(c, v, v')
  ensures LeaderReceivedPromisesImpliesAcceptorState(c, v')
  decreases c, v, v'
{
  VariableNextProperties(c, v, v');
}

// modified: 23 lines
// Needs receive invaraint skolemization
lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{ 
  forall ldr, acc, lnr, vb:ValBal, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr) && c.ValidAcceptorIdx(acc) && c.ValidLearnerIdx(lnr)
    && vb in v'.History(i).learners[lnr].receivedAccepts.m
    && vb.b < ldr
    && v'.History(i).leaders[ldr].HeardAtMost(vb.b)
    && acc in v'.History(i).leaders[ldr].ReceivedPromises()
  ensures
    acc !in v'.History(i).learners[lnr].receivedAccepts.m[vb]
  {
    MessageInvInductive(c, v, v');
    MonotonicityInvInductive(c, v, v');
    if acc in v'.History(i).learners[lnr].receivedAccepts.m[vb] {
      var acceptMsg := AcceptMessageExistence(c, v', i, lnr, vb, acc);
      var prom := PromiseMessageExistence(c, v', i, ldr, acc);
    }
  }
}

// modified: 14 lines
lemma AcceptMessageExistence(c: Constants, v: Variables, i: int, lnr:LearnerId, vb: ValBal, acc: AcceptorId) 
  returns (acceptMsg : Message)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  requires vb in v.History(i).learners[lnr].receivedAccepts.m
  requires LearnerHost.ReceiveAcceptTrigger(c.learners[lnr], v.History(i).learners[lnr], acc, vb)
  requires ReceiveAcceptValidity(c, v)
  ensures acceptMsg in v.network.sentMsgs
  ensures acceptMsg == Accept(vb, acc)
{
  reveal_ReceiveAcceptValidity();
  acceptMsg := Accept(vb, acc);
}

// modified: 25 lines
lemma PromiseMessageExistence(c: Constants, v: Variables, i: int, ldr: LeaderId, acc: AcceptorId) 
  returns (promiseMsg : Message)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLeaderIdx(ldr)
  requires LeaderHostHighestHeardBallotMonotonic(c, v)
  requires LeaderHost.ReceivePromiseTrigger(c.leaders[ldr], v.History(i).leaders[ldr], acc)
  requires ReceivePromiseValidity(c, v)
  ensures   && promiseMsg.Promise?
            && promiseMsg in v.network.sentMsgs
            && promiseMsg.bal == ldr
            && promiseMsg.acc == acc
            && (promiseMsg.vbOpt.Some? ==> 
                && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
                && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value)
{
  reveal_ReceivePromiseValidity();
  promiseMsg :| && promiseMsg.Promise?
                && promiseMsg in v.network.sentMsgs
                && promiseMsg.bal == ldr
                && promiseMsg.acc == acc
                && (promiseMsg.vbOpt.Some? ==> 
                    && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
                    && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value);
}

// modified: 58 lines
lemma {:timeLimitMultiplier 2} InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires Next(c, v, v')
  requires LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
  requires LearnerReceivedAcceptImpliesAccepted(c, v')
  ensures ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
{
  forall vb, ldr:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && Chosen(c, v'.History(i), vb)
    && c.ValidLeaderIdx(ldr)
    && vb.b < ldr
    && v'.History(i).LeaderCanPropose(c, ldr)
  ensures
    v'.History(i).leaders[ldr].HeardAtLeast(vb.b)
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      var lc, l, l' := c.leaders[ldr], v.Last().leaders[ldr], v'.Last().leaders[ldr];
      if dsStep.LeaderHostStep? {
        // Note that proof is identical to sync case
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
        if ldr == dsStep.actor {  // if the leader in question is now taking a step
          assert Chosen(c, v.Last(), vb);  // trigger
          var choosingAccs := SupportingAcceptorsForChosen(c, v, vb);
          var h, h' := v.Last(), v'.Last();
          if h.leaders[ldr].HeardAtMost(vb.b) {
            //Ldr has yet to see ballot b in this step. By quorum intersection, it must see
            // an acceptor in choosingAccs in this step
            var acc := dsStep.msgOps.recv.value.acc;
            if acc !in choosingAccs {
              // In this case, by quorum intersection, acc must already be in ldr.receivePromises
              // Because, choosingAccs !! v.leaders[ldr].ReceivedPromises()
              var allAccs := GetAcceptorSet(c, v);
              var e := QuorumIntersection(allAccs, choosingAccs, h.leaders[ldr].ReceivedPromises() + {acc});
              assert false;
            }      
          }    
        }
      } else if dsStep.AcceptorHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        // Note that proof is identical to sync case
        if !Chosen(c, v.Last(), vb) {
          var actor, msgOps := dsStep.actor, dsStep.msgOps;
          var lnr:LearnerId:| ChosenAtLearner(c, v'.Last(), vb, lnr);
          if lnr == actor {
            var choosingAccs := SupportingAcceptorsForChosen(c, v', vb);
            // These properties of choosingAccs carry over to pre-state v
            assert v.Last().LeaderCanPropose(c, ldr);  // trigger
            if !v.Last().leaders[ldr].HeardAtLeast(vb.b) {
              var allAccs := GetAcceptorSet(c, v);
              var e := QuorumIntersection(allAccs, choosingAccs, v.Last().leaders[ldr].ReceivedPromises());
              assert false;
            } 
          } else {
            assert !ChosenAtLearner(c, v.Last(), vb, lnr);  // trigger
          }
        }
      }
    }
  }
}

// modified: 31 lines
lemma InvNextChosenValImpliesAcceptorOnlyAcceptsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires AcceptorValidPromisedAndAccepted(c, v')  // prereq for AcceptorAcceptedImpliesProposed
  
  // prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires AcceptorAcceptedImpliesProposed(c, v')
  requires OneValuePerBallotLeaderAndLearners(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')

  // post-condition
  ensures ChosenValImpliesAcceptorOnlyAcceptsVal(c, v')
{
  forall vb, acc:AcceptorId, i | 
    && v'.ValidHistoryIdx(i)
    && Chosen(c, v'.History(i), vb)
    && c.ValidAcceptorIdx(acc)
    && v'.History(i).acceptors[acc].HasAcceptedAtLeastBal(vb.b)
  ensures
     v'.History(i).acceptors[acc].acceptedVB.value.v == vb.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var actor, msgOps := dsStep.actor, dsStep.msgOps;
      if dsStep.LeaderHostStep? || (dsStep.AcceptorHostStep? && actor == acc) {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if v'.History(i).acceptors[acc].acceptedVB.value.v != vb.v {
        LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', v'.Last().acceptors[acc].acceptedVB.value.b, vb);
      }
    }
  }
}

// modified: 28 lines
lemma InvNextChosenValImpliesLeaderOnlyHearsVal(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')

  // Prereqs for LeaderHearsDifferentValueFromChosenImpliesFalse
  requires OneValuePerBallotLeaderAndLearners(c, v')
  requires LeaderHighestHeardUpperBound(c, v')
  requires LeaderHearedImpliesProposed(c, v')
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v')
  ensures ChosenValImpliesLeaderOnlyHearsVal(c, v')
{
  forall vb, ldrBal:LeaderId, i | 
    && v'.ValidHistoryIdx(i)
    && Chosen(c, v'.History(i), vb)
    && c.ValidLeaderIdx(ldrBal)
    && v'.History(i).leaders[ldrBal].HeardAtLeast(vb.b)
  ensures
    v'.History(i).leaders[ldrBal].Value() == vb.v
  {
    VariableNextProperties(c, v, v');
    if i == |v'.history| - 1 {
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      if dsStep.LeaderHostStep? || dsStep.AcceptorHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if v'.History(i).leaders[ldrBal].Value() != vb.v {
        LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
      }
    }
  }
}


/***************************************************************************************
*                                    Helper Lemmas                                     *
***************************************************************************************/

lemma LeaderHearsDifferentValueFromChosenImpliesFalse(c: Constants, v: Variables, ldr: LeaderId, chosen: ValBal)
  requires v.WF(c)
  requires Chosen(c, v.Last(), chosen)
  requires c.ValidLeaderIdx(ldr)
  requires v.Last().leaders[ldr].highestHeardBallot.MNSome?
  requires v.Last().leaders[ldr].highestHeardBallot.value >= chosen.b
  requires v.Last().leaders[ldr].Value() != chosen.v
  requires chosen.b < ldr
  requires OneValuePerBallotLeaderAndLearners(c, v)
  requires LeaderHighestHeardUpperBound(c, v)
  requires LeaderHearedImpliesProposed(c, v)
  requires ChosenImpliesProposingLeaderHearsChosenBallot(c, v)
  ensures false
  decreases c, v, ldr, chosen
{
  ghost var ldr' := v.Last().leaders[ldr].highestHeardBallot.value;
  assert v.Last().leaders[ldr'].Value() == v.Last().leaders[ldr].Value();
  assert chosen.b <= ldr' < ldr;
  LeaderHearsDifferentValueFromChosenImpliesFalse(c, v, ldr', chosen);
}

lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value)
    returns (vb: ValBal)
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires v.Last().learners[lnr].HasLearnedValue(val)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures vb.v == val
  ensures Chosen(c, v.Last(), vb)
  decreases c, v, lnr
{
  ghost var bal :| ChosenAtLearner(c, v.Last(), VB(val, bal), lnr);
  return VB(val, bal);
}

lemma InvImpliesAtMostOneChosenVal(c: Constants, v: Variables)
  requires v.WF(c)
  requires ProtocolInv(c, v)
  ensures AtMostOneChosenVal(c, v)
  decreases c, v
{
}

lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneChosenVal(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
  ensures Safety(c, v)
  decreases c, v
{
  if !Safety(c, v) {
    ghost var l1, l2 :| c.ValidLearnerIdx(l1) && c.ValidLearnerIdx(l2) && v.Last().learners[l1].learned.Some? && v.Last().learners[l2].learned.Some? && v.Last().learners[l1].learned != v.Last().learners[l2].learned;
    ghost var vb1 := LearnedImpliesChosen(c, v, l1, v.Last().learners[l1].learned.value);
    ghost var vb2 := LearnedImpliesChosen(c, v, l2, v.Last().learners[l2].learned.value);
    assert false;
  }
}

// modified: 13 lines
lemma NewChosenOnlyInLearnerStep(c: Constants, v: Variables, v': Variables, dsStep: Step) 
  requires v.WF(c)
  requires Next(c, v, v')
  requires NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep)
  requires !dsStep.LearnerHostStep?
  ensures forall vb | Chosen(c, v'.Last(), vb) :: Chosen(c, v.Last(), vb)
{
  forall vb | Chosen(c, v'.Last(), vb) 
  ensures Chosen(c, v'.history[|v'.history|-2], vb) {
    var lnr:LearnerId :| ChosenAtLearner(c, v'.Last(), vb, lnr);   // witness
    assert ChosenAtLearner(c, v.Last(), vb, lnr);                  // trigger
  }
}

lemma SupportingAcceptorsForChosen(c: Constants, v: Variables, vb: ValBal)
    returns (supportingAccs: set<AcceptorId>)
  requires v.WF(c)
  requires Chosen(c, v.Last(), vb)
  requires LearnerReceivedAcceptImpliesAccepted(c, v)
  ensures |supportingAccs| >= c.f + 1
  ensures forall a: int
   
 | a in supportingAccs :: c.ValidAcceptorIdx(a) && v.Last().acceptors[a].HasAcceptedAtLeastBal(vb.b)
  ensures exists lnr: int
 :: c.ValidLearnerIdx(lnr) && vb in v.Last().learners[lnr].receivedAccepts.m && supportingAccs <= v.Last().learners[lnr].receivedAccepts.m[vb]
  decreases c, v, vb
{
  ghost var lnr: LearnerId :| ChosenAtLearner(c, v.Last(), vb, lnr);
  supportingAccs := v.Last().learners[lnr].receivedAccepts.m[vb];
  return supportingAccs;
}

lemma GetAcceptorSet(c: Constants, v: Variables) returns (accSet: set<AcceptorId>)
  requires v.WF(c)
  ensures forall a: int
  
 :: c.ValidAcceptorIdx(a) <==> a in accSet
  ensures |accSet| == 2 * c.f + 1
  decreases c, v
{
  accSet := set a: int | 0 <= a < |c.acceptors|;
  SetComprehensionSize(|c.acceptors|);
}


/***************************************************************************************
*                                  Helper Functions                                    *
***************************************************************************************/

ghost predicate OneValuePerBallotLeaderAndLearners(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall ldr: int, lnr: int, acceptedVal: Value, i: nat
 {:trigger v.History(i).learners[lnr], VB(acceptedVal, ldr)} {:trigger VB(acceptedVal, ldr), c.ValidLearnerIdx(lnr), v.ValidHistoryIdx(i)}
 | v.ValidHistoryIdx(i) && c.ValidLeaderIdx(ldr) && c.ValidLearnerIdx(lnr) && VB(acceptedVal, ldr) in v.History(i).learners[lnr].receivedAccepts.m :: 
    acceptedVal == v.History(i).leaders[ldr].Value()
}

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>)
  decreases c, quorum
{
  |quorum| >= c.f + 1 &&
  forall id: int
 {:trigger c.ValidAcceptorIdx(id)} {:trigger id in quorum}
 | id in quorum :: 
    c.ValidAcceptorIdx(id)
}

ghost predicate AtMostOneChosenVal(c: Constants, v: Variables)
  requires v.WF(c)
  decreases c, v
{
  forall vb1: ValBal, vb2: ValBal, i: nat
 {:trigger vb2.v, vb1.v, v.ValidHistoryIdx(i)} {:trigger vb2.v, vb1.b, v.ValidHistoryIdx(i)} {:trigger vb2.v, Chosen(c, v.History(i), vb1)} {:trigger vb1.v, vb2.b, v.ValidHistoryIdx(i)} {:trigger vb1.v, Chosen(c, v.History(i), vb2)} {:trigger vb2.b, vb1.b, v.ValidHistoryIdx(i)} {:trigger vb2.b, Chosen(c, v.History(i), vb1)} {:trigger vb1.b, Chosen(c, v.History(i), vb2)} {:trigger Chosen(c, v.History(i), vb2), Chosen(c, v.History(i), vb1)}
 | v.ValidHistoryIdx(i) && Chosen(c, v.History(i), vb1) && Chosen(c, v.History(i), vb2) :: 
    c.ValidLeaderIdx(vb1.b) &&
    c.ValidLeaderIdx(vb2.b) &&
    vb1.v == vb2.v
}


// I am special
ghost predicate Chosen(c: Constants, v: Hosts, vb: ValBal)
  requires v.WF(c)
  decreases c, v, vb
{
  exists lnr: LearnerId
 :: 
    ChosenAtLearner(c, v, vb, lnr)
}

// I am special
ghost predicate ChosenAtLearner(c: Constants, v: Hosts, vb: ValBal, lnr: LearnerId)
  requires v.WF(c)
  decreases c, v, vb, lnr
{
  c.ValidLearnerIdx(lnr) &&
  vb in v.learners[lnr].receivedAccepts.m &&
  IsAcceptorQuorum(c, v.learners[lnr].receivedAccepts.m[vb])
}


} // end module ProofDraft
