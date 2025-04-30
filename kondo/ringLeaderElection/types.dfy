include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Message = Msg(val: nat, src: nat) {
    ghost function Src() : nat {
      src
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
} // end module Types
