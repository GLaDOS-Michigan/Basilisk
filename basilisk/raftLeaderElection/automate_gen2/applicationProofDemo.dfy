include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"
include "customMessageInvariants.dfy"

module ReduceProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants
import opened MonotonicityInvariants
import opened CustomMessageInvariants

ghost predicate RegularInvs(c: Constants, v: Variables) {
  && MonotonicityInv(c, v)
  && MessageInv(c, v)
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
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  MonotonicityInvInductive(c, v, v');
  MessageInvInductive(c, v, v');
  RegularInvImpliesSafety(c, v');
}

/***************************************************************************************
*                                       Proofs                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF


lemma RegularInvImpliesSafety(c: Constants, v: Variables) 
  requires RegularInvs(c, v)
  ensures Safety(c, v)
{
    forall l1:nat, l2:nat |
      && c.ValidHostIdx(l1)
      && c.ValidHostIdx(l2)
      && v.Last().hosts[l1].status.Leader?
      && v.Last().hosts[l2].status.Leader?
      && l1 != l2
      ensures v.Last().hosts[l1].ms.term != v.Last().hosts[l2].ms.term{
        var commonAcc := GetIntersectingAcceptor(c, v, l1, l2);
        if commonAcc != l1 && commonAcc != l2{
          var _, inMsg1 := Custom1ReceiveVoteStepSkolemization(c, v, |v.history| - 1, l1, commonAcc, v.Last().hosts[l1].ms.term);
          var _, inMsg2 := Custom1ReceiveVoteStepSkolemization(c, v, |v.history| - 1, l2, commonAcc, v.Last().hosts[l2].ms.term);
          var j1, _ := SendVoteSkolemization(c, v, inMsg1);
          var j2, _ := SendVoteSkolemization(c, v, inMsg2);
          // assert v.History(j1+1).hosts[inMsg1.Src()].ms.term == v.Last().hosts[l1].ms.term;
          // assert v.History(j2+1).hosts[inMsg2.Src()].ms.term == v.Last().hosts[l2].ms.term;
          // if j1 + 1 <= j2 +1 && v.Last().hosts[l1].ms.term == v.Last().hosts[l2].ms.term {
          //   assert v.History(j2+1).hosts[inMsg1.Src()].ms.SatisfiesMonotonic(v.History(j1+1).hosts[inMsg2.Src()].ms);
          //   assert v.History(j2+1).hosts[inMsg1.Src()].ms.votedFor == v.History(j1+1).hosts[inMsg2.Src()].ms.votedFor;
          //   assert v.Last().hosts[l1].ms.term != v.Last().hosts[l2].ms.term;
          // }
          // else if j2 + 1 <= j1 +1 && v.Last().hosts[l1].ms.term == v.Last().hosts[l2].ms.term{
          //   assert v.History(j1+1).hosts[inMsg1.Src()].ms.SatisfiesMonotonic(v.History(j2+1).hosts[inMsg2.Src()].ms);
          //   assert v.History(j2+1).hosts[inMsg1.Src()].ms.votedFor == v.History(j1+1).hosts[inMsg2.Src()].ms.votedFor;
          //   assert v.Last().hosts[l1].ms.term != v.Last().hosts[l2].ms.term;
          // }
          // assert v.Last().hosts[l1].ms.term != v.Last().hosts[l2].ms.term;

        }
        else if commonAcc == l1 {
          var _, inMsg := Custom1ReceiveVoteStepSkolemization(c, v, |v.history| - 1, l2, commonAcc, v.Last().hosts[l2].ms.term);
        }
        else{
          var _, inMsg := Custom1ReceiveVoteStepSkolemization(c, v, |v.history| - 1, l1, commonAcc, v.Last().hosts[l1].ms.term);
        }
      }
}

lemma GetIntersectingAcceptor(c: Constants, v: Variables, l1: nat, l2: nat)
returns (accId: HostId)
  requires v.WF(c)
  requires RegularInvs(c, v)
  requires c.ValidHostIdx(l1)
  requires c.ValidHostIdx(l2)
  requires v.Last().hosts[l1].status.Leader?
  requires v.Last().hosts[l2].status.Leader?
  ensures accId in v.Last().hosts[l1].ms.acceptors && accId in v.Last().hosts[l2].ms.acceptors
{
    var j1, _, _ := Custom2SendDeclareStepSkolemization(c, v, |v.history| - 1, l1, v.Last().hosts[l1].ms);
    var j2, _, _ := Custom2SendDeclareStepSkolemization(c, v, |v.history| - 1, l2, v.Last().hosts[l2].ms);
    // assert |v.History(j1).hosts[l1].ms.acceptors| >= c.f + 1;
    // assert |v.History(j2).hosts[l2].ms.acceptors| >= c.f + 1;
    // assert v.History(j1).hosts[l1].ms == v.Last().hosts[l1].ms;
    // assert v.History(j2).hosts[l2].ms == v.Last().hosts[l2].ms;
    var allAccs := set id | 0 <= id < 2*c.f+1;
    SetComprehensionSize(2*c.f+1);
    forall i:nat | i in v.History(j1).hosts[l1].ms.acceptors ensures i in allAccs{
      if i != c.hosts[l1].idx {
        var _, msg := Custom1ReceiveVoteStepSkolemization(c, v, j1, l1, i, v.History(j1).hosts[l1].ms.term);
        // assert ValidMessages(c, v);
      }
    }
    forall i:nat | i in v.History(j2).hosts[l2].ms.acceptors ensures i in allAccs{
      if i != c.hosts[l2].idx{
        var _, msg := Custom1ReceiveVoteStepSkolemization(c, v, j2, l2, i, v.History(j2).hosts[l2].ms.term);
        // assert ValidMessages(c, v);
      }
    }
    accId := QuorumIntersection(allAccs , v.History(j1).hosts[l1].ms.acceptors, v.History(j2).hosts[l2].ms.acceptors);
}
// END SAFETY PROOF

}  // end module ReduceProof

