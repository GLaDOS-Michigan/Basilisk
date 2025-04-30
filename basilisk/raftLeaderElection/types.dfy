include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message = VoteReq(term:nat, candidate: nat) | Vote(term: nat, voter: nat, candidate: nat) | Declare(term: nat, leader: nat) {
    ghost function Src() : nat {
      match this{
        case VoteReq(_, _) => this.candidate
        case Vote(_, _, _) => this.voter
        case Declare(_, _) => this.leader
      }
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

}