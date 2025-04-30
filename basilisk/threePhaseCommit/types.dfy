include "../lib/MonotonicityLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Vote = Yes | No

  datatype Decision = Commit | Abort

  datatype Message =
    VoteReq | Vote(v: Vote, src: HostId) | Decide(decision: Decision) | Precommit | Precommitack(src: HostId)
  {
    ghost function Src() : nat {
      if this.Vote? then src else if this.Precommitack? then src else 0
    }
  }

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

}
