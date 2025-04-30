include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module MultiPaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened CustomMessageInvariants
import opened Obligations

ghost predicate RegularInvs(c: Constants, v: Variables) {
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ValidVariables(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && RegularInvs(c, v)
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
{
  VariableNextProperties(c, v, v');
  MessageInvInductive(c, v, v');
  MonotonicityInvInductive(c, v, v');
  SafetyProof(c, v, v');
}


/***************************************************************************************
*                                       Proofs                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

// We allow safety to be proven inductively
lemma SafetyProof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires RegularInvs(c, v')
  ensures Safety(c, v')
{
  if !AtMostOneChosenValAllSlots(c, v') {
    var badSlot, vb1, vb2 :| 
                    && c.ValidSlot(badSlot)
                    && ChosenAtSlot(c, v'.Last(), vb1, badSlot) 
                    && ChosenAtSlot(c, v'.Last(), vb2, badSlot)
                    && !( && c.ValidHostIdx(vb1.b.id)
                          && c.ValidHostIdx(vb2.b.id)
                          && vb1.v == vb2.v);
    ChosenImpliesValidBallot(c, v', |v'.history|-1, vb1, badSlot);
    ChosenImpliesValidBallot(c, v', |v'.history|-1, vb2, badSlot);
    assert vb1.v != vb2.v;

    // vb1.b < vb2.b
    if BalLt(vb1.b, vb2.b) {
      var propMsg := ChosenImpliesProposed(c, v', |v'.history|-1, vb2, badSlot);
      var promQ, hb := GetPromiseQuorumForProposeMessage(c, v', vb1, propMsg, vb2.b, vb2.v);
      SafetyProofBallotInduction(c, v', vb1, vb2, promQ, hb, badSlot);
    } // vb1.b > vb2.b 
    else if BalLt(vb2.b, vb1.b) {
      var propMsg := ChosenImpliesProposed(c, v', |v'.history|-1, vb1, badSlot);
      var promQ, hb := GetPromiseQuorumForProposeMessage(c, v', vb2, propMsg, vb1.b, vb1.v);
      SafetyProofBallotInduction(c, v', vb2, vb1, promQ, hb, badSlot);
    } else {
      // Proves that at most one chosen value at each ballot
      var propMsg1 := ChosenImpliesProposed(c, v', |v'.history|-1, vb1, badSlot);
      var propMsg2 := ChosenImpliesProposed(c, v', |v'.history|-1, vb2, badSlot);
      assert propMsg1.val == propMsg2.val;  // trigger
    }
    assert false;  // trigger
  }
  AtMostOneChosenImpliesSafety(c, v');
}

lemma {:timeLimitMultiplier 2} SafetyProofBallotInduction(c: Constants, v: Variables, vb1: ValBal, vb2: ValBal, promQ: set<Message>, hb: Ballot, slot: nat)
  requires RegularInvs(c, v)
  // Pre-conditions on arguments
  requires c.ValidSlot(slot)
  requires ChosenAtSlot(c, v.Last(), vb1, slot)
  requires IsPromiseQuorum(c, v, promQ, vb2.b)
  requires PromiseSetHighestVBAtSlot(c, v, promQ, vb2.b, VB(vb2.v, hb), slot)
  // vb1.b <= hb < vb2.b
  requires BalLteq(vb1.b, hb)
  requires BalLt(hb, vb2.b)
  // Post-conditions
  ensures vb1.v == vb2.v
  decreases vb2.b.x
  decreases vb2.b.id
{
  /* Proof sketch:
      vb1 has a quorum of Accept messages. Hence, every acceptor in vb1 has accepted some
      ballot at least as large as b1.

      vb2 has a quorum of Promise messages. Hence, every acceptor in vb2 has promised some
      ballot at least as large as b2. 

      vb2 Promise quorum shares an acceptor with vb1 accept quorum. As such, the Promise
      quorum's highest witnessed accept ballot hb must be in the range vb1.b <= hb < vb2.b.

      Consider an induction on ballot number:
      1. The witnessed accept at hb has value vb1. Then we are done.
      
      2. Else, there is an Accept message for (vb2.v, hb) Then there is a hb promise quorum
         with value vb2.v. Recursively descend b3 to get contradiction.
  */

  var hm :| WinningPromiseMessageInSlotQuorum(c, v, promQ, vb2.b, slot, VB(vb2.v, hb), hm);
  if hm.logAcceptedVB.vbOptSeq[slot].value.v == vb1.v {
    return;  // base case
  } else {
    // Obtain fact that vb1.b <= hb
    var vb1witness := ChosenImpliesSeenByHigherPromiseQuorum(c, v, vb1, vb2.b, promQ, slot);

    // Skolemize the Propose message associated with hm
    var promiser := hm.Src();
    var i, _ := SendPromiseSkolemization(c, v, hm);
    reveal_ValidHistory();
    var _, propMsg, _ := ReceiveProposeSendAcceptStepSkolemization(c, v, i, promiser, slot, Some(VB(vb2.v, hb)));
    
    if hb == vb1.b {
      // hb is highest ballot seen by vb2.b promise quorum
      // vb1.b is the chosen ballot. 
      // Want to show that witnessed value is vb1.v
      var propMsg1 := ChosenImpliesProposed(c, v, |v.history|-1, vb1, slot);      
      assert propMsg.val == propMsg1.val;     // trigger
      assert false;
    } else {
      // Do induction
      var nq, nb := GetPromiseQuorumForProposeMessage(c, v, vb1, propMsg, hb, vb2.v);
      SafetyProofBallotInduction(c, v, vb1, VB(vb2.v, hb), nq, nb, slot);
    }
  }
}

lemma {:timeLimitMultiplier 2} GetPromiseQuorumForProposeMessage(c: Constants, v: Variables, chosenVB: ValBal, propMsg: Message, bal: Ballot, val: Value)
returns (promQ: set<Message>, hb: Ballot)
  requires v.WF(c)
  requires ValidVariables(c, v)
  requires ValidMessages(c, v)
  requires SendProposeValidity(c, v)
  requires HostReceiveValidity(c, v)
  requires HostLsMonotonic(c, v)
  requires SendPromiseValidity(c, v)
  requires SendAcceptValidity(c, v)
  requires HostPromisedMonotonic(c, v)
  requires HostLogAcceptedVBMonotonic(c, v)

  // Pre-conditions on arguments
  requires IsProposeMessage(v, propMsg) && c.ValidSlot(propMsg.slot)
  requires ChosenAtSlot(c, v.Last(), chosenVB, propMsg.slot)
  requires propMsg.val == val
  requires propMsg.bal == bal
  requires BalLt(chosenVB.b, bal)
  // Post-conditions
  ensures IsPromiseQuorum(c, v, promQ, bal)
  ensures PromiseSetHighestVBAtSlot(c, v, promQ, bal, VB(val, hb), propMsg.slot)
  // chosenVB.b <= hb < bal
  ensures BalLteq(chosenVB.b, hb)
  ensures BalLt(hb, bal)
{
  var i :|  && v.ValidHistoryIdxStrict(i)
            && Host.SendPropose(c.hosts[bal.id], v.History(i).hosts[bal.id], v.History(i+1).hosts[bal.id], propMsg);
  
  var hm : Message;
  promQ := HighestHeardBackedByReceivedPromises(c, v, i, bal, propMsg.slot);
  var slot := propMsg.slot;
  var choosingWitness := ChosenImpliesSeenByHigherPromiseQuorum(c, v, chosenVB, bal, promQ, slot);
  hm :| WinningPromiseMessageInSlotQuorum(c, v, promQ, bal, slot, VB(v.History(i).hosts[bal.id].LdrValue(slot), v.History(i).hosts[bal.id].ls.logHighestHeardValues[slot].ob.value), hm);
  hb := hm.logAcceptedVB.vbOptSeq[slot].value.b;
}

// Corresponds to ChosenValImpliesPromiseQuorumSeesBal in manual proof
lemma ChosenImpliesSeenByHigherPromiseQuorum(c: Constants, v: Variables, chosenVB: ValBal, promBal: Ballot, promQ: set<Message>, slot: nat)
returns (promMsg: Message) 
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires ValidMessages(c, v)
  requires SendPromiseValidity(c, v)
  requires SendAcceptValidity(c, v)
  requires HostReceiveValidity(c, v)
  requires HostPromisedMonotonic(c, v)
  requires HostLogAcceptedVBMonotonic(c, v)

  // Pre-conditions on arguments
  requires c.ValidSlot(slot)
  requires ChosenAtSlot(c, v.Last(), chosenVB, slot)
  requires IsPromiseQuorum(c, v, promQ, promBal)
  requires BalLt(chosenVB.b, promBal)
  // Post-conditions
  ensures IsPromiseMessage(v, promMsg)
  ensures promMsg in promQ
  ensures promMsg.logAcceptedVB.vbOptSeq[slot].Some?
  ensures BalLteq(chosenVB.b, promMsg.logAcceptedVB.vbOptSeq[slot].value.b)
{
  /* Proof sketch:
    - Chosen implies there are f+1 Accept messages for chosenVB. For each of these
      acceptor sources, there is some point in history that it accepted chosenVB.

    - Promise quorum implies that f+1 hosts promised promBal. For each of these 
      acceptor sources, there is some point in history that it promised promBal.

    - For each acceptor in intersection, let j, i be the respective points in history.
      If j < i, then the Promise message witnesses chosenVB as accepted.
      Else if i < j, then acceptor can never accept chosenVB. Contradiction
  */

  // Get Accept quorum
  reveal_ChosenAtLearnerSlot();
  var lnr: nat :| ChosenAtLearnerSlot(c, v.Last(), chosenVB, lnr, slot);
  var accQ := ExtractAcceptMessagesFromReceivedAccepts(c, v, v.Last().hosts[lnr].logReceivedAccepts.mapSeq[slot][chosenVB], chosenVB, lnr, slot);

  // Skolemize the intersecting acceptor and its messages
  var acc := GetIntersectingAcceptor(c, v, accQ, chosenVB, promQ, promBal, slot);
  var accMsg :| accMsg in accQ && accMsg.acc == acc && accMsg.slot == slot;
  promMsg :| promMsg in promQ && promMsg.acc == acc;

  var i, inMsg := SendPromiseSkolemization(c, v, promMsg);
  var j, propMsg := SendAcceptSkolemization(c, v, accMsg);
  // Helper needed to avoid timeout
  ChosenImpliesSeenByHigherPromiseQuorumHelper(c, v, chosenVB, inMsg, promMsg, promBal, i, propMsg, accMsg, j, slot);
}

lemma ChosenImpliesSeenByHigherPromiseQuorumHelper(c: Constants, v: Variables, chosenVB: ValBal, inMsg: Message, promMsg: Message, promBal: Ballot, i: nat, propMsg: Message, accMsg: Message, j: nat, slot: nat) 
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires HostPromisedMonotonic(c, v)
  requires HostLogAcceptedVBMonotonic(c, v)

  // Pre-conditions on arguments
  requires c.ValidSlot(slot)
  requires IsPromiseMessage(v, promMsg)
  requires IsAcceptMessage(v, accMsg) && accMsg.slot == slot
  requires IsProposeMessage(v, propMsg) && propMsg.slot == slot
  requires accMsg.vb == chosenVB
  requires promMsg.acc == accMsg.acc
  requires BalLt(chosenVB.b, promBal)
  requires promMsg.bal == promBal
  requires v.ValidHistoryIdxStrict(i)
  requires v.ValidHistoryIdxStrict(j)
  requires Host.ReceivePrepareSendPromise(c.hosts[promMsg.Src()], v.History(i).hosts[promMsg.Src()], v.History(i+1).hosts[promMsg.Src()], inMsg, promMsg)
  requires Host.ReceiveProposeSendAccept(c.hosts[accMsg.Src()], v.History(j).hosts[accMsg.Src()], v.History(j+1).hosts[accMsg.Src()], propMsg, accMsg)
  // Post-conditions
  ensures promMsg.logAcceptedVB.vbOptSeq[slot].Some?
  ensures BalLteq(chosenVB.b, promMsg.logAcceptedVB.vbOptSeq[slot].value.b)
{}

lemma GetIntersectingAcceptor(c: Constants, v: Variables, accQ: set<Message>, accVB: ValBal,  promQ: set<Message>, promBal: Ballot, slot: nat)
returns (accId: HostId)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires IsPromiseQuorum(c, v, promQ, promBal)
  requires c.ValidSlot(slot)
  requires IsAcceptQuorumAtSlot(c, v, accQ, accVB, slot)
  ensures exists promise, accept :: 
    && promise in promQ
    && accept in accQ
    && promise.acc == accId
    && accept.acc == accId
{
  var prAccs := AcceptorsFromPromiseSet(c, v, promQ, promBal);
  var acAccs := AcceptorsFromAcceptSet(c, v, accQ, accVB, slot);
  var allAccs := set id | 0 <= id < 2*c.f+1;
  SetComprehensionSize(2*c.f+1);
  var commonAcc := QuorumIntersection(allAccs , prAccs, acAccs);
  return commonAcc;
}

lemma AcceptorsFromPromiseSet(c: Constants, v: Variables, promSet: set<Message>, promBal: Ballot) 
returns (accs: set<HostId>)
  requires IsPromiseSet(c, v, promSet, promBal)
  ensures forall a | a in accs 
    :: (exists pr :: pr in promSet && pr.acc == a)
  ensures |accs| == |promSet|
{
  reveal_MessageSetDistinctAccs();
  if |promSet| == 0 {
    accs := {};
  } else {
    var p :| p in promSet;
    var accs' := AcceptorsFromPromiseSet(c, v, promSet-{p}, promBal);
    accs := accs' + {p.acc};
  }
}

lemma AcceptorsFromAcceptSet(c: Constants, v: Variables, accSet: set<Message>, vb: ValBal, slot: nat)
returns (accs: set<HostId>)  
  requires IsAcceptSet(c, v, accSet, vb, slot)
  requires c.ValidSlot(slot)
  ensures forall a | a in accs 
    :: (exists ac :: ac in accSet && ac.acc == a && ac.slot == slot)
  ensures |accs| == |accSet|
{
  if |accSet| == 0 {
    accs := {};
  } else {
    var a :| a in accSet;
    var accs' := AcceptorsFromAcceptSet(c, v, accSet-{a}, vb, slot);
    accs := accs' + {a.acc};
  }
}

lemma ExtractAcceptMessagesFromReceivedAccepts(c: Constants, v: Variables, receivedAccepts: set<HostId>, vb: ValBal, lnr: HostId, slot: nat)
returns (acceptMsgs: set<Message>)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires HostReceiveValidity(c, v)
  requires 0 <= lnr < |c.hosts|
  requires c.ValidSlot(slot)
  requires vb in v.Last().hosts[lnr].logReceivedAccepts.mapSeq[slot]
  requires receivedAccepts <= v.Last().hosts[lnr].logReceivedAccepts.mapSeq[slot][vb]
  ensures |acceptMsgs| == |receivedAccepts|
  ensures forall m | m in acceptMsgs :: IsAcceptMessage(v, m) && m.vb == vb && m.slot == slot
  ensures MessageSetDistinctAccs(acceptMsgs)
  ensures forall acc :: (acc in receivedAccepts <==> Accept(slot, vb, acc) in acceptMsgs)
  decreases receivedAccepts
{
  reveal_MessageSetDistinctAccs();
  if | receivedAccepts | == 0 {
    acceptMsgs := {};
  } else {
    var x :| x in receivedAccepts;
    var subset := ExtractAcceptMessagesFromReceivedAccepts(c, v, receivedAccepts - {x}, vb, lnr, slot);
    reveal_ValidHistory();
    var i, msg := ReceiveAcceptStepSkolemization(c, v, |v.history|-1, lnr, slot, vb, x);
    acceptMsgs := subset + {msg};
  }
}

lemma HighestHeardBackedByReceivedPromises(c: Constants, v: Variables, i: nat, ldrBal: Ballot, slot: nat)
returns (promS: set<Message>)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires HostReceiveValidity(c, v)
  requires HostLsMonotonic(c, v)
  
  requires v.ValidHistoryIdx(i)
  requires c.ValidHostIdx(ldrBal.id)
  requires c.ValidSlot(slot)
  requires v.History(i).hosts[ldrBal.id].ls.currBal == ldrBal
  ensures LeaderPromiseSetPropertiesAtSlot(c, v, i, ldrBal, promS, slot)
{
  promS := {};

  var ldr := v.History(i).hosts[ldrBal.id];
  var hbal := ldr.ls.logHighestHeardValues[slot].ob;

  var accs :=  ldr.LdrReceivedPromises();
  reveal_MessageSetDistinctAccs();

  if hbal.Some? {
    assert ldr.ls.currBal == ldrBal;

    reveal_ValidHistory();
    var j, hm := Custom2ReceivePromiseStepSkolemization(c, v, i, ldrBal.id, ldrBal, ldr.LdrValue(slot), hbal.value, slot);
    promS := promS + {hm};
    accs := accs - {hm.acc};
    assert MessageSetDistinctAccs(promS);  // trigger

    while |accs| > 0 
      invariant |promS| + |accs| == |ldr.LdrReceivedPromises()|
      invariant forall p | p in promS :: p.Promise?
      invariant forall acc | acc in accs :: (forall m | m in promS :: m.acc != acc)
      invariant IsPromiseSet(c, v, promS, ldr.ls.currBal)
      invariant hbal.None? ==> PromiseSetEmptyVBAtSlot(c, v, promS, ldr.ls.currBal, slot)
      invariant MessageSetDistinctAccs(promS)
      invariant forall p: Message | p in promS :: p.acc in ldr.LdrReceivedPromises()
      invariant WinningPromiseMessageInSlotQuorum(c, v, promS, ldrBal, slot, VB(ldr.LdrValue(slot), hbal.value), hm)
      decreases accs
    {
      var acc :| acc in accs;
      var p := PromiseMessageExistenceAtSlot(c, v, i, ldrBal, acc, slot);
      promS := promS + {p};
      accs := accs - {acc};
      assert MessageSetDistinctAccs(promS);  // trigger
    }
  } else {
    assert MessageSetDistinctAccs(promS);  // trigger
    while |accs| > 0 
      invariant |promS| + |accs| == |ldr.LdrReceivedPromises()|
      invariant forall p | p in promS :: p.Promise?
      invariant forall acc | acc in accs :: (forall m | m in promS :: m.acc != acc)
      invariant IsPromiseSet(c, v, promS, ldr.ls.currBal)
      invariant hbal.None? ==> PromiseSetEmptyVBAtSlot(c, v, promS, ldr.ls.currBal, slot)
      invariant MessageSetDistinctAccs(promS)
      invariant forall p: Message | p in promS :: p.acc in ldr.LdrReceivedPromises()
      decreases accs
    {
      var acc :| acc in accs;
      reveal_ValidHistory();
      var p := PromiseMessageExistenceAtSlot(c, v, i, ldrBal, acc, slot);
      promS := promS + {p};
      accs := accs - {acc};
      assert MessageSetDistinctAccs(promS);  // trigger
    }
  }
}

lemma PromiseMessageExistenceAtSlot(c: Constants, v: Variables, i: int, ldrBal: Ballot, acc: HostId, slot: nat) 
  returns (promiseMsg : Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidHostIdx(ldrBal.id)
  requires c.ValidSlot(slot)
  requires HostLsMonotonic(c, v)
  requires HostReceiveValidity(c, v)
  requires ReceivePromiseReceivePreempt1ReceivePreempt2WitnessCondition(c, v, i, ldrBal.id, slot, v.History(i).hosts[ldrBal.id].ls.logHighestHeardValues[slot], acc)
  requires v.History(i).hosts[ldrBal.id].ls.currBal == ldrBal
  ensures   && promiseMsg.Promise?
            && promiseMsg in v.network.sentMsgs
            && promiseMsg.bal == ldrBal
            && promiseMsg.acc == acc
            && |promiseMsg.logAcceptedVB.vbOptSeq| == c.logCap
            && (promiseMsg.logAcceptedVB.vbOptSeq[slot].Some? ==> 
                && v.History(i).hosts[ldrBal.id].ls.logHighestHeardValues[slot].ob.Some?
                && BalLteq(promiseMsg.logAcceptedVB.vbOptSeq[slot].value.b, v.History(i).hosts[ldrBal.id].ls.logHighestHeardValues[slot].ob.value)  
            )
{
  reveal_ValidHistory();
  var j, m := Custom1ReceivePromiseStepSkolemization(c, v, i, ldrBal.id, ldrBal, acc);
  promiseMsg := m;
}

lemma ChosenImpliesProposed(c: Constants, v: Variables, i: nat, vb: ValBal, slot: nat) 
returns (proposeMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires ValidMessages(c, v)
  requires SendAcceptValidity(c, v)
  requires HostReceiveValidity(c, v)
  requires c.ValidSlot(slot)
  requires v.ValidHistoryIdx(i)
  requires ChosenAtSlot(c, v.History(i), vb, slot)
  ensures proposeMsg in v.network.sentMsgs
  ensures proposeMsg == Propose(slot, vb.b, vb.v)
{
  reveal_ChosenAtLearnerSlot();
  var lnr: nat :| ChosenAtLearnerSlot(c, v.History(i), vb, lnr, slot);
  var acc :| acc in v.History(i).hosts[lnr].logReceivedAccepts.mapSeq[slot][vb];
  reveal_ValidHistory();
  var j, accMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, slot, vb, acc);
  var k, prop := SendAcceptSkolemization(c, v, accMsg);
  return prop;
}

lemma ChosenImpliesValidBallot(c: Constants, v: Variables, i: nat, vb: ValBal, slot: nat)
  requires RegularInvs(c, v)
  requires c.ValidSlot(slot)
  requires v.ValidHistoryIdx(i)
  requires ChosenAtSlot(c, v.History(i), vb, slot)
  ensures c.ValidHostIdx(vb.b.id)
{
  reveal_ChosenAtLearnerSlot();
  var lnr: nat :| ChosenAtLearnerSlot(c, v.History(i), vb, lnr, slot);
  var acc :| acc in v.History(i).hosts[lnr].logReceivedAccepts.mapSeq[slot][vb];
  reveal_ValidHistory();
  var j, accMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, slot, vb, acc);
  var k, propMsg := SendAcceptSkolemization(c, v, accMsg);
}

lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  requires AtMostOneChosenValAllSlots(c, v)
  ensures Safety(c, v)
{
  if !Safety(c, v) {
    ghost var slot, l1, l2 :| 
        && c.ValidHostIdx(l1) && c.ValidHostIdx(l2) && c.ValidSlot(slot) 
        && v.Last().hosts[l1].logLearned[slot].Some? 
        && v.Last().hosts[l2].logLearned[slot].Some? 
        && v.Last().hosts[l1].logLearned[slot] != v.Last().hosts[l2].logLearned[slot];
    ghost var vb1 := LearnedAtSlotImpliesChosenAtSlot(c, v, l1, v.Last().hosts[l1].logLearned[slot].value, slot);
    ghost var vb2 := LearnedAtSlotImpliesChosenAtSlot(c, v, l2, v.Last().hosts[l2].logLearned[slot].value, slot);
    // contradiction, assert false
  }
}

lemma LearnedAtSlotImpliesChosenAtSlot(c: Constants, v: Variables, lnr: HostId, val: Value, slot: nat) returns (vb: ValBal)
  requires RegularInvs(c, v)
  requires c.ValidHostIdx(lnr)
  requires c.ValidSlot(slot)
  requires v.Last().hosts[lnr].HasLearnedValueAtSlot(val, slot)
  ensures vb.v == val
  ensures ChosenAtSlot(c, v.Last(), vb, slot)
{
  LearnedAtSlotImpliesQuorumOfAccepts(c, v, lnr, val, slot);
  ghost var bal :| ChosenAtLearnerSlot(c, v.Last(), VB(val, bal), lnr, slot);
  return VB(val, bal);
}

lemma LearnedAtSlotImpliesQuorumOfAccepts(c: Constants, v: Variables, lnr: HostId, val: Value, slot: nat) 
  requires RegularInvs(c, v)
  requires c.ValidHostIdx(lnr)
  requires c.ValidSlot(slot)
  requires v.Last().hosts[lnr].HasLearnedValueAtSlot(val, slot)
  ensures exists b: Ballot :: ChosenAtLearnerSlot(c, v.Last(), VB(val, b), lnr, slot)
{
    reveal_ValidHistory();
    reveal_ChosenAtLearnerSlot();
    var i, step, msgOps := NextLearnStepStepSkolemization(c, v, |v.history|-1, lnr, slot, v.Last().hosts[lnr].logLearned[slot]);
    LearnerValidReceivedAcceptsAtSlot(c, v, i, lnr, slot);
    LearnerValidReceivedAcceptsAtSlot(c, v, |v.history|-1, lnr, slot);
}

lemma LearnerValidReceivedAcceptsAtSlot(c: Constants, v: Variables, i: nat, lnr: HostId, slot: nat) 
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires ValidMessages(c, v)
  requires HostReceiveValidity(c, v)
  requires HostLogReceivedAcceptsMonotonic(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidHostIdx(lnr)
  requires c.ValidSlot(slot)
  ensures forall vb, acc |  && vb in v.History(i).hosts[lnr].logReceivedAccepts.mapSeq[slot]
                            && acc in v.History(i).hosts[lnr].logReceivedAccepts.mapSeq[slot][vb]
          :: c.ValidHostIdx(acc)
{
  forall vb, acc |
    && vb in v.History(i).hosts[lnr].logReceivedAccepts.mapSeq[slot]
    && acc in v.History(i).hosts[lnr].logReceivedAccepts.mapSeq[slot][vb]
  ensures c.ValidHostIdx(acc) {
    reveal_ValidHistory();
    var j, accMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, slot, vb, acc);
  }
}

/***************************************************************************************
*                                  Helper Definitions                                  *
***************************************************************************************/


ghost predicate ChosenAtSlot(c: Constants, v: Hosts, vb: ValBal, slot: nat)
  requires v.WF(c)
  requires c.ValidSlot(slot)
{
  exists lnr :: ChosenAtLearnerSlot(c, v, vb, lnr, slot)
}

ghost predicate {:opaque} ChosenAtLearnerSlot(c: Constants, v: Hosts, vb: ValBal, lnr: HostId, slot: nat)
  requires v.WF(c)
  requires c.ValidSlot(slot)
{
  && c.ValidHostIdx(lnr)
  && vb in v.hosts[lnr].logReceivedAccepts.mapSeq[slot]
  && IsAcceptorQuorum(c, v.hosts[lnr].logReceivedAccepts.mapSeq[slot][vb])
}

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<HostId>) {
  && |quorum| >= c.f + 1
  && (forall id: HostId | id in quorum :: c.ValidHostIdx(id))
}

ghost predicate AtMostOneChosenValAtSlot(c: Constants, v: Variables, slot: nat)
  requires v.WF(c)
  requires c.ValidSlot(slot)
{
  forall vb1, vb2 | 
    && ChosenAtSlot(c, v.Last(), vb1, slot)
    && ChosenAtSlot(c, v.Last(), vb2, slot)
  :: 
    && c.ValidHostIdx(vb1.b.id)
    && c.ValidHostIdx(vb2.b.id)
    && vb1.v == vb2.v
}

// Foremost safety condition
ghost predicate AtMostOneChosenValAllSlots(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall slot | c.ValidSlot(slot) :: AtMostOneChosenValAtSlot(c, v, slot)
}

ghost predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

ghost predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}

ghost predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

ghost predicate {:opaque} MessageSetDistinctAccs(mset: set<Message>) 
  requires forall m | m in mset :: m.Promise? || m.Accept?
{
  forall m1, m2 | m1 in mset && m2 in mset && m1.acc == m2.acc
      :: m1 == m2
}

ghost predicate IsPromiseSet(c: Constants, v: Variables, pset: set<Message>, bal: Ballot) {
  && (forall m | m in pset ::
    && IsPromiseMessage(v, m)
    && m.bal == bal
    && |m.logAcceptedVB.vbOptSeq| == c.logCap
  )
  && MessageSetDistinctAccs(pset)
}

ghost predicate IsPromiseQuorum(c: Constants, v: Variables, quorum: set<Message>, bal: Ballot) {
  && |quorum| >= c.f+1
  && IsPromiseSet(c, v, quorum, bal)
}

ghost predicate WinningPromiseMessageInSlotQuorum(c: Constants, v: Variables, pset: set<Message>, qbal: Ballot, slot:nat, hsvb: ValBal, m: Message)
  requires c.ValidSlot(slot)
  requires IsPromiseSet(c, v, pset, qbal)
{
    && m in pset 
    && m.logAcceptedVB.vbOptSeq[slot] == Some(hsvb)
    && (forall other: Message | 
        && other in pset  
        && 0 <= slot < |other.logAcceptedVB.vbOptSeq|
        && other.logAcceptedVB.vbOptSeq[slot].Some?
      :: BalLteq(other.logAcceptedVB.vbOptSeq[slot].value.b, hsvb.b))
}

ghost predicate PromiseSetHighestVBAtSlot(c: Constants, v: Variables, pset: set<Message>, qbal: Ballot, hsvb: ValBal, slot: nat)
  requires c.ValidSlot(slot)
  requires IsPromiseSet(c, v, pset, qbal)
{
  exists m :: WinningPromiseMessageInSlotQuorum(c, v, pset, qbal, slot, hsvb, m)
}

ghost predicate PromiseSetEmptyVBAtSlot(c: Constants, v: Variables, pset: set<Message>, qbal: Ballot, slot: nat)
  requires c.ValidSlot(slot)
  requires IsPromiseSet(c, v, pset, qbal)
{
  forall m | m in pset :: m.logAcceptedVB.vbOptSeq[slot] == None
}


ghost predicate LeaderPromiseSetPropertiesAtSlot(c: Constants, v: Variables, i: nat, ldrBal: Ballot, promS: set<Message>, slot: nat) 
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidHostIdx(ldrBal.id)
  requires c.ValidSlot(slot)
  requires v.History(i).hosts[ldrBal.id].ls.currBal == ldrBal
{
    && var ldr := v.History(i).hosts[ldrBal.id];
    && var cldr := c.hosts[ldrBal.id];
    && var hbal := ldr.ls.logHighestHeardValues[slot].ob;
    && IsPromiseSet(c, v, promS, ldr.ls.currBal)
    && (hbal.Some? ==> PromiseSetHighestVBAtSlot(c, v, promS, ldr.ls.currBal, VB(ldr.LdrValue(slot), hbal.value), slot))
    && (hbal.None? ==> PromiseSetEmptyVBAtSlot(c, v, promS, ldr.ls.currBal, slot))
    && |promS| == |ldr.LdrReceivedPromises()|
}

ghost predicate IsAcceptSet(c: Constants, v: Variables, accSet: set<Message>, vb: ValBal, slot: nat) {
  forall m | m in accSet ::
    && IsAcceptMessage(v, m)
    && m.vb == vb
    && m.slot == slot
}

ghost predicate IsAcceptQuorumAtSlot(c: Constants, v: Variables, quorum: set<Message>, vb: ValBal, slot: nat) {
  && |quorum| >= c.f+1
  && IsAcceptSet(c, v, quorum, vb, slot)
  && MessageSetDistinctAccs(quorum)
}

// END SAFETY PROOF

} // end module MultiPaxosProof
