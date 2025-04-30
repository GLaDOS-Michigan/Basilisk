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
                | Promise(bal:Ballot, acc:HostId, vbOpt:Option<ValBal>)  //valbal is the value-ballot pair with which the value was accepted
                | Propose(bal:Ballot, val:Value)
                | Accept(vb:ValBal, acc:HostId)
                // Preempt1 and Preempt2 comes from Kondo's restriction of one message type per send action
                | Preempt1(acc:HostId, ldr:HostId, bal: Ballot) // acc is the source, ldr is the dest, and Ballot is the promised ballot at acc
                | Preempt2(acc:HostId, ldr:HostId, bal: Ballot) // acc is the source, ldr is the dest, and Ballot is the promised ballot at acc
{
  ghost function Src() : nat {
    match this {
      case Prepare(bal) => bal.id
      case Promise(_, acc, _) => acc
      case Propose(bal, _) => bal.id
      case Accept(_, acc) => acc
      case Preempt1(acc, _, _) => acc
      case Preempt2(acc, _, _) => acc
    }
  }
}

datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

datatype PendingPrepare = PendingPrepare(bal: Ballot)

/// Some custom monotonic datatypes

datatype MonotonicVBOption = MVBSome(value: ValBal) | MVBNone
{
  ghost predicate SatisfiesMonotonic(past: MonotonicVBOption) {
    past.MVBSome? ==> (this.MVBSome? && BalLteq(past.value.b, this.value.b))
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

datatype MonotonicLeaderState = LS(currBal: Ballot, value: Value, promises: set<HostId>, highestHeardBallot: Option<Ballot>, f: nat)
{
  ghost predicate SatisfiesMonotonic(past: MonotonicLeaderState) {
    && BalLteq(past.currBal, currBal)
    && (past.currBal == currBal ==> 
            && past.promises <= this.promises
            && |past.promises| <= |this.promises|
            && (forall val: Value | |past.promises| >= f+1 && past.value == val
                :: this.value == val
            )
            && (past.highestHeardBallot.Some? ==> this.highestHeardBallot.Some? && BalLteq(past.highestHeardBallot.value, this.highestHeardBallot.value))
      )
  }
}

datatype MonotonicBallotOption = MBSome(bal: Ballot) | MBNone
{
  ghost predicate SatisfiesMonotonic(past: MonotonicBallotOption) {
    past.MBSome? ==> (this.MBSome? && BalLteq(past.bal, this.bal))
  }
}

}