include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Vote = Yes | No

  datatype Decision = Commit | Abort

  datatype Message =
    VoteReqMsg | VoteMsg(v: Vote, src: HostId) | DecideMsg(decision: Decision)
  {
    ghost function Src() : nat {
      if this.VoteMsg? then src else 0
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
