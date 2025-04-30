include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Request = Req(clientId: ClientId, reqId: nat)

  datatype Message =
    RequestMsg(r: Request) | ResponseMsg(r: Request)
  {
    ghost function Src() : nat {
      if this.RequestMsg? then r.clientId else 0
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