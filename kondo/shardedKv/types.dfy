include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat
  type UniqueKey = int
  datatype Entry = Entry(live: bool, version: nat)

  datatype Message = Reconf(src: nat, dst: nat, key: UniqueKey, version: nat) {
    function Src() : nat {
      src
    }

    function Dst() : nat {
      dst
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