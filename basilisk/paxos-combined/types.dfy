include "../lib/MonotonicityLibrary.dfy"

module Types {
import opened UtilitiesLibrary

type HostId = nat


type Value(!new, ==)
datatype ValBal = VB(v:Value, b:HostId)

datatype Message = Prepare(bal:HostId)
                | Promise(bal:HostId, acc:HostId, vbOpt:Option<ValBal>)  //valbal is the value-ballot pair with which the value was accepted
                | Propose(bal:HostId, val:Value)
                | Accept(vb:ValBal, acc:HostId)                 
{
  ghost function Src() : nat {
    if this.Prepare? then bal
    else if this.Promise? then acc
    else if this.Propose? then bal
    else acc
  }
}

datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

datatype PendingPrepare = PendingPrepare(bal:HostId)

/// Some custom monotonic datatypes

datatype MonotonicVBOption = MVBSome(value: ValBal) | MVBNone
{
  ghost predicate SatisfiesMonotonic(past: MonotonicVBOption) {
    past.MVBSome? ==> (this.MVBSome? && past.value.b <= this.value.b)
  }

  ghost function ToOption() : Option<ValBal> {
    if this.MVBNone? then None
    else Some(this.value)
  }
}

datatype MonotonicReceivedAccepts = RA(m: map<ValBal, set<HostId>>) 
{
  ghost predicate SatisfiesMonotonic(past: MonotonicReceivedAccepts) {
    forall vb | 
    && vb in past.m 
    :: 
      && 0 < |past.m[vb]|
      && vb in this.m
      && past.m[vb] <= this.m[vb]
      && |past.m[vb]| <= |this.m[vb]|
  }
}

datatype MonotonicPromisesAndValue = PV(promises: set<HostId>, value: Value, f: nat) 
{
  ghost predicate SatisfiesMonotonic(past: MonotonicPromisesAndValue) {
    && past.promises <= this.promises
    && |past.promises| <= |this.promises|
    && (forall val: Value | |past.promises| >= f+1 && past.value == val
        :: this.value == val
    )
  }
}
}