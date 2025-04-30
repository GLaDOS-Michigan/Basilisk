include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type ClientId = nat
  
  datatype Request = Req(clientId: ClientId, reqId: nat)

  datatype Message =
    Request(r: Request) | Response(r: Request)
  {
    ghost function Src() : nat {
      if this.Request? then r.clientId else 0
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

} // end module Types