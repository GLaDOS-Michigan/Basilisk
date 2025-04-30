include "../lib/MonotonicityLibrary.dfy"
include "types.dfy"

module Host {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary

  datatype Step = LocalSumStep | SendSumStep | RecvSumStep | GlobalSumStep
  datatype Constants = Constants(idx: nat, grp_size: nat, arr : seq<int>)
  {
    ghost predicate WF(){
      && idx < grp_size
      && grp_size > 0
    }
  }
    
  datatype Variables = Variables(
    globalSum: Option<int>,
    sum: Option<int>,
    peerSums : seq<Option<int>>
  )
  {
    ghost predicate WF(c: Constants){
      && c.WF()
      && |peerSums| == if c.idx == 0 then c.grp_size else 0
    }
  }


  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && (|grp_c| > 0)
    && (|grp_c| == |grp_v|)
    && (forall idx | 0 <= idx < |grp_c| :: 
      && (grp_c[idx].idx == idx && grp_c[idx].grp_size == |grp_c|)
      && (grp_v[idx].WF(grp_c[idx])))
  }
  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && (GroupWF(grp_c, grp_v))
    && (forall idx | 0 <= idx < |grp_v| :: 
      && (grp_v[idx].sum.None?)
      && (forall i:nat | i < |grp_v[idx].peerSums| :: grp_v[idx].peerSums[i].None?)
      && (grp_v[idx].globalSum.None?))
  }


  ghost predicate NextLocalSumStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v.WF(c)
    && msgOps == MessageOps(None, None)
    && v.sum.None?
    && v' == v.(sum := Some(Sum(c.arr)))
  }

  ghost predicate NextTransferStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendTransferSum(c, v, v', msgOps.send.value)
  }

  ghost predicate SendTransferSum(c: Constants, v: Variables, v': Variables, outMsg: Message) {
    && v.WF(c)
    && v.sum.Some?
    && v' == v
    && outMsg == TransferSum(v.sum.value, c.idx)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v.WF(c)
    && msgOps.recv.Some?
    && msgOps.send.None?
    && ReceiveTransferSum(c, v, v', msgOps.recv.value)
  }

  ghost predicate ReceiveTransferSum(c: Constants, v: Variables, v': Variables, inMsg: Message) {
    && v.WF(c)
    && c.idx == 0
    && inMsg.TransferSum?
    && 0 <= inMsg.idx < c.grp_size
    && v.peerSums[inMsg.idx].None?
    && v' == v.(peerSums := v.peerSums[inMsg.idx := Some(inMsg.sum)])
  }

  ghost function OptionSum(arr: seq<Option<int>>) : int
    requires forall i:nat | i < |arr| :: arr[i].Some?
  {
    if |arr| == 0 then 0 else arr[0].value + OptionSum(arr[1..])
  }

  ghost predicate NextGlobalSumStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v.WF(c)
    && c.idx == 0
    && msgOps.recv.None?
    && msgOps.send.None?
    && v.globalSum.None?
    && (forall i:nat | i < c.grp_size :: v.peerSums[i].Some?)
    && v' == v.(globalSum := Some(OptionSum(v.peerSums)))
  }


  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step {
      case LocalSumStep => NextLocalSumStep(c, v, v', msgOps)
      case SendSumStep => NextTransferStep(c, v, v', msgOps)
      case RecvSumStep => NextReceiveStep(c, v, v', msgOps)
      case GlobalSumStep => NextGlobalSumStep(c, v, v', msgOps)
    }
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }


}

