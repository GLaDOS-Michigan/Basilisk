include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message =
    VoteReq(candidate: HostId) | Vote(voter: HostId, candidate: HostId) 
  {
    ghost function Src() : nat {
      match this {
        case VoteReq(candidate) => candidate
        case Vote(voter, _) => voter
      }
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

  datatype Transmit = Transmit(m: Message) {
    function Send() : MessageOps {
      MessageOps(None, Some(m))
    }

    function Recv() : MessageOps {
      MessageOps(Some(m), None)
    }
  }
}