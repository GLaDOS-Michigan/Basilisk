# Notes

Generates async proof from sync proof.

## Commands

Generate monotonicity and message invariants:

```bash
./local-dafny/Scripts/dafny /msgInvs distributedSystem.dfy
```

Generate async draft proof:

```bash
./local-dafny/Scripts/dafny /genAsyncProof ../centralized/applicationProof.dfy
```

The following lemmas are manually added or modified:

```dafny
lemma InvNextLearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, v': Variables) 
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires LearnerValidReceivedAccepts(c, v)
  requires LearnedImpliesQuorumOfAccepts(c, v)
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

lemma InvNextLeaderHighestHeardToPromisedRangeHasNoAccepts(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures LeaderHighestHeardToPromisedRangeHasNoAccepts(c, v')
{ 
  forall ldr, acc, lnr, vb:ValBal, i | 
    && v'.ValidHistoryIdx(i)
    && c.ValidLeaderIdx(ldr)
    && c.ValidAcceptorIdx(acc)
    && c.ValidLearnerIdx(lnr)
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

lemma AcceptMessageExistence(c: Constants, v: Variables, i: int, lnr:LearnerId, vb: ValBal, acc: AcceptorId) 
  returns (acceptMsg : Message)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  requires vb in v.History(i).learners[lnr].receivedAccepts.m
  requires LearnerHost.ReceiveAcceptTrigger(c.learners[lnr], v.History(i).learners[lnr], acc, vb)
  requires ReceiveAcceptValidity(c, v)  // custom receive invariant
  ensures acceptMsg in v.network.sentMsgs
  ensures acceptMsg == Accept(vb, acc)
{
  reveal_ReceiveAcceptValidity();
  acceptMsg := Accept(vb, acc);
}

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
                && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
            )
{
  reveal_ReceivePromiseValidity();
  promiseMsg :| && promiseMsg.Promise?
                && promiseMsg in v.network.sentMsgs
                && promiseMsg.bal == ldr
                && promiseMsg.acc == acc
                && (promiseMsg.vbOpt.Some? ==> 
                    && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
                    && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
                );
}

lemma InvNextChosenImpliesProposingLeaderHearsChosenBallot(c: Constants, v: Variables, v': Variables) 
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
          assert Chosen(c, v.Last(), vb);
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
      if dsStep.LeaderHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if dsStep.AcceptorHostStep? && actor == acc {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        if v'.History(i).acceptors[acc].acceptedVB.value.v != vb.v {
          var ldr := v'.Last().acceptors[acc].acceptedVB.value.b;
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldr, vb);
        }
      }
    }
  }
}

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
      if dsStep.LeaderHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else if dsStep.AcceptorHostStep? {
        NewChosenOnlyInLearnerStep(c, v, v', dsStep);
      } else {
        if v'.History(i).leaders[ldrBal].Value() != vb.v {
          LeaderHearsDifferentValueFromChosenImpliesFalse(c, v', ldrBal, vb);
        }
      }
    }
  }
}

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
```
