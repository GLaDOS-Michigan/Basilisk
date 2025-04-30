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

} // end module Types
