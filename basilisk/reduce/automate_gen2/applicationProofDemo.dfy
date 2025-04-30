include "monotonicityInvariantsAutogen.dfy"
include "messageInvariantsAutogen.dfy"

module ReduceProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants
import opened MonotonicityInvariants

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
  InvNextSafety(c, v, v');
}

/***************************************************************************************
*                                       Proofs                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

lemma sequenceSumLemma(hosts: seq<Host.Constants>, peerSums: seq<Option<int>>)
  requires |peerSums| == |hosts|
  requires forall i:nat | i < |peerSums| :: peerSums[i] == Some(Sum(hosts[i].arr))
  ensures DistributedSystem.Host.OptionSum(peerSums) == Sum(SumOfSequences(hosts))
{
  if(|hosts| != 0) {
    SumLemma2(hosts[0].arr, SumOfSequences(hosts[1..]));
    sequenceSumLemma(hosts[1..], peerSums[1..]);
  }   

}

lemma InvNextSafety(c: Constants, v: Variables, v': Variables) 
  requires Inv(c, v)
  requires MessageInv(c, v')
  requires Next(c, v, v')
  ensures Safety(c, v')
{
  var l, l' := v.Last().hosts[0], v'.Last().hosts[0];
  if l'.globalSum.Some? {
    reveal_ValidHistory();
    var i, step, msgOps := NextGlobalSumStepStepSkolemization(c, v', |v'.history|-1, 0, l'.globalSum);
    // Assert that every member of globalSum is correct host local sum.
    if l.globalSum.None? {
      forall j:nat | j<|l.peerSums| ensures l.peerSums[j] == Some(Sum(c.hosts[j].arr)){
        var _, msg := ReceiveTransferSumStepSkolemization(c, v, |v.history| - 1, 0, j, l.peerSums[j]);
        var k := SendTransferSumSkolemization(c, v, msg);
        var _, _, _ := NextLocalSumStepStepSkolemization(c, v, k, j, v.History(k).hosts[j].sum);
      }
      sequenceSumLemma(c.hosts, l.peerSums);
    }
  }
}

// END SAFETY PROOF

}  // end module ReduceProof

