include "types.dfy"

module Host {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(numParticipants:nat, ringPos: nat, hostId: HostId)

  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat, ringPos: HostId)
  {
    && c.numParticipants == participantCount
    && c.ringPos == ringPos
  }

  datatype Variables = Variables(
    highestHeard: int
  )
  {
    ghost predicate WF(c: Constants) {
      && 0 < c.numParticipants
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall ringPos: nat | ringPos < |grp_c|
        :: ConstantsValidForGroup(grp_c[ringPos], |grp_c|, ringPos))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.highestHeard == -1
  }

  datatype Step =
    TransmissionStep() | ReceiveStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case TransmissionStep => NextTransmissionStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
  }

  ghost predicate NextTransmissionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF(c)
  {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendMsg(c, v, v', msgOps.send.value)
  }

  /***
      sendPredicate: hosts, Msg
  ***/
  ghost predicate SendMsg(c: Constants, v: Variables, v': Variables, msg: Message)
  {
    && msg.src == c.ringPos
    && msg.val == max(v.highestHeard, c.hostId) // max of what I heard vs my own hostId
    && v == v'
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveMsg(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveMsg(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.highestHeard < msg.val
    && msg.src < c.numParticipants
    && c.ringPos == Successor(c.numParticipants, msg.src)
    // update v'
    && v' == v.(
        highestHeard := msg.val
    )
  }

  // Receive msg trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveMsgTrigger(c: Constants, v: Variables, hh: nat) {
    && hh >= 0
    && v.highestHeard == hh
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host
