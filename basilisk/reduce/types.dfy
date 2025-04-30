include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message = TransferSum(sum :int, idx: nat) {
    ghost function Src() : nat {
      idx
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

  datatype MonotonicFixedArray = MonotonicFixedArray(arr: seq<Option<int>>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicFixedArray) {
      && |past.arr| == |arr|
      && forall i | 0 <= i < |arr| && past.arr[i].Some? ::
        past.arr[i] == this.arr[i]
    }
}
}