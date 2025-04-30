include "messageInvariantsAutogen.dfy"

module RingLeaderElectionProof {
import opened Types
import opened UtilitiesLibrary
import opened DistributedSystem
import opened Obligations
import opened MessageInvariants

ghost predicate RegularInvs(c: Constants, v: Variables) {
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
  MessageInvInductive(c, v, v');
  MessageInvariantsImplyChordDominates(c, v');
}

/***************************************************************************************
*                                       Proofs                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

ghost predicate Between(start: nat, node: nat, end: nat) 
{
  if start < end then
    start < node < end else
    node < end || start < node
}

function Distance(n: nat, start: nat, end: nat) : nat
  requires 0 <= start < n
  requires 0 <= end < n
{
  if start <= end then end - start 
  else n - start + end
}

ghost predicate ChordDominates(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall src:nat, dst:nat, mid:nat | 
      && c.ValidIdx(src)
      && c.ValidIdx(dst)
      && c.ValidIdx(mid)
      && v.Last().hosts[dst].highestHeard == c.hosts[src].hostId
      && Between(src, mid, dst)
    :: 
      c.hosts[mid].hostId < c.hosts[src].hostId
}

lemma MessageInvariantsImplyChordDominates(c: Constants, v: Variables)
  requires MessageInv(c, v)
  ensures ChordDominates(c, v)
{
  forall src:nat, dst:nat, mid:nat | 
    && c.ValidIdx(src)
    && c.ValidIdx(dst)
    && c.ValidIdx(mid)
    && v.Last().hosts[dst].highestHeard == c.hosts[src].hostId
    && Between(src, mid, dst)
  ensures
    c.hosts[mid].hostId < c.hosts[src].hostId
  {
    reveal_ValidHistory();
    var j, step, msgOps := HostReceiveSkolemization(c, v, |v.history|-1, dst);
    if Predecessor(|c.hosts|, dst) != mid {
      MidMustHaveSentSrcHostId(c, v, src, mid, dst);
    }
  }
}

lemma MidMustHaveSentSrcHostId(c: Constants, v: Variables, src: nat, mid: nat, dst: nat) 
  requires MessageInv(c, v)
  requires c.ValidIdx(src)
  requires c.ValidIdx(dst)
  requires c.ValidIdx(mid)
  requires v.Last().hosts[dst].highestHeard == c.hosts[src].hostId
  requires Between(src, mid, dst)
  ensures Msg(c.hosts[src].hostId, mid) in v.network.sentMsgs 
  decreases Distance(|c.hosts|, mid, dst)
{
  LemmaSentNotMyIdImpliesReceivedId(c, v);
  var n := |c.hosts|;
  if mid == Predecessor(n, dst) {
    reveal_ValidHistory();
    var j, step, msgOps := HostReceiveSkolemization(c, v, |v.history|-1, dst);
  } else {
    MidMustHaveSentSrcHostId(c, v, src, Successor(n, mid), dst);
  }
}

ghost predicate SentNotMyIdImpliesReceivedId(c: Constants, v: Variables) 
  requires MessageInv(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.val != c.hosts[msg.src].hostId 
  :: Msg(msg.val, Predecessor(|c.hosts|, msg.src)) in v.network.sentMsgs
}

lemma LemmaSentNotMyIdImpliesReceivedId(c: Constants, v: Variables)
  requires MessageInv(c, v)
  ensures SentNotMyIdImpliesReceivedId(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.val != c.hosts[msg.src].hostId 
  ensures Msg(msg.val, Predecessor(|c.hosts|, msg.src)) in v.network.sentMsgs
  {
    var i, _ := SendMsgSkolemization(c, v, msg);
  }
}

// END SAFETY PROOF

}  // end module RingLeaderElectionProof

