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

  datatype Step = ReceiveStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.Some?
    && msgOps.recv.Some?
    && ReceiveMsgSendMsg(c, v, v', msgOps.recv.value, msgOps.send.value)
  }

  // Receive-Send predicate
  ghost predicate ReceiveMsgSendMsg(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
    // enabling conditions
    && v.highestHeard < inMsg.val
    && inMsg.src < c.numParticipants
    && c.ringPos == Successor(c.numParticipants, inMsg.src)
    // update v' and specify outMsg
    && outMsg == Msg(max(inMsg.val, c.hostId), c.ringPos)
    && v' == v.(
        highestHeard := inMsg.val
    )
  }

  // Receive msg trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveMsgTrigger(c: Constants, v: Variables, hh: nat) {
    && v.highestHeard == hh
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host
