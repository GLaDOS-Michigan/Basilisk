include "../lib/MonotonicityLibrary.dfy"

module Types {
import opened UtilitiesLibrary

type HostId = nat

type Value(!new, ==)

datatype Ballot = Bal(x: nat, id: HostId)

// function NextBallotForHost(currBal: Ballot) : Ballot {
//   Bal(currBal.x+1, currBal.id)
// }

function BalLt(b1: Ballot, b2: Ballot): bool {
  b1.x < b2.x || (b1.x == b2.x && b1.id < b2.id)
}

function BalLteq(b1: Ballot, b2: Ballot): bool {
  b1 == b2 || BalLt(b1, b2)
}

datatype ValBal = VB(v:Value, b:Ballot)
datatype Message = Prepare(bal:Ballot)
                | Promise(bal:Ballot, acc:HostId, logAcceptedVB:MonotonicVBOptionSeq)  // accepted value for each slot
                | Propose(slot: int, bal:Ballot, val:Value)
                | Accept(slot: int, vb:ValBal, acc:HostId)
                // Preempt1 and Preempt2 comes from Kondo's restriction of one message type per send action
                | Preempt1(acc:HostId, ldr:HostId, bal: Ballot) // acc is the source, ldr is the dest, and Ballot is the promised ballot at acc
                | Preempt2(acc:HostId, ldr:HostId, bal: Ballot) // acc is the source, ldr is the dest, and Ballot is the promised ballot at acc
{
  ghost function Src() : nat {
    match this {
      case Prepare(bal) => bal.id
      case Promise(_, acc, _) => acc
      case Propose(_, bal, _) => bal.id
      case Accept(_, _, acc) => acc
      case Preempt1(acc, _, _) => acc
      case Preempt2(acc, _, _) => acc
    }
  }
}

datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

datatype PendingPrepare = PendingPrepare(bal: Ballot)

/// Some custom monotonic datatypes

datatype MonotonicVBOptionSeq = MVBSeq(vbOptSeq: seq<Option<ValBal>>)
{

  function getSlot(slot: int) : Option<ValBal>
    requires 0 <= slot < |vbOptSeq|
  {
    this.vbOptSeq[slot]
  }

  function updateSlot(slot: int, item: Option<ValBal>) : MonotonicVBOptionSeq 
    requires 0 <= slot < |vbOptSeq|
  {
    MVBSeq(vbOptSeq[slot := item])
  }

  ghost predicate SatisfiesMonotonic(past: MonotonicVBOptionSeq) {
    && |past.vbOptSeq| == |this.vbOptSeq|
    && (forall slot | 0 <= slot < |this.vbOptSeq| && past.getSlot(slot).Some? ::
          this.getSlot(slot).Some? && BalLteq(past.getSlot(slot).value.b, this.getSlot(slot).value.b)
    )
  }
}

datatype MonotonicReceivedAcceptsSeq = RASeq(mapSeq: seq<map<ValBal, set<HostId>>>)
{
  function getSlot(slot: int) : map<ValBal, set<HostId>>
    requires 0 <= slot < |mapSeq|
  {
    this.mapSeq[slot]
  }

  function updateSlot(slot: int, item: map<ValBal, set<HostId>>) : MonotonicReceivedAcceptsSeq 
    requires 0 <= slot < |mapSeq|
  {
    RASeq(mapSeq[slot := item])
  }

  ghost predicate SatisfiesMonotonic(past: MonotonicReceivedAcceptsSeq) {
    && |past.mapSeq| == |this.mapSeq|
    && (forall slot, vb | 0 <= slot < |this.mapSeq| && vb in past.getSlot(slot) 
        :: 
        && 0 < |past.getSlot(slot)[vb]|
        && vb in this.getSlot(slot)
        && past.getSlot(slot)[vb] <= this.getSlot(slot)[vb]
        && |past.getSlot(slot)[vb]| <= |this.getSlot(slot)[vb]|
    )
  }
}

datatype HighestHeard = HH(ob: Option<Ballot>, v: Value)

datatype MonotonicLeaderState = LS(
    currBal: Ballot, 
    promises: set<HostId>, 
    logHighestHeardValues: seq<HighestHeard>, 
    f: nat
) {
  ghost predicate SatisfiesMonotonic(past: MonotonicLeaderState) {
    && BalLteq(past.currBal, currBal)
    && SatisfiesMonotonicPromises(past)
    && SatisfiesMonotonicHighestHeardValues(past)
  }

  ghost predicate SatisfiesMonotonicPromises(past: MonotonicLeaderState) {
    past.currBal == currBal ==> (
            && past.promises <= this.promises
            && |past.promises| <= |this.promises|
    )
  }

  ghost predicate SatisfiesMonotonicHighestHeardValues(past: MonotonicLeaderState) {
    && |past.logHighestHeardValues| == |this.logHighestHeardValues|
    && past.currBal == currBal ==>
        && (forall slot | 0 <= slot < |logHighestHeardValues| && |past.promises| >= f+1
                :: this.logHighestHeardValues[slot] == past.logHighestHeardValues[slot])
        && (forall slot | 0 <= slot < |logHighestHeardValues| && past.logHighestHeardValues[slot].ob.Some? 
                :: this.logHighestHeardValues[slot].ob.Some? && BalLteq(past.logHighestHeardValues[slot].ob.value, this.logHighestHeardValues[slot].ob.value))
  }
}

datatype MonotonicBallotOption = MBSome(bal: Ballot) | MBNone
{
  ghost predicate SatisfiesMonotonic(past: MonotonicBallotOption) {
    past.MBSome? ==> (this.MBSome? && BalLteq(past.bal, this.bal))
  }
}

}