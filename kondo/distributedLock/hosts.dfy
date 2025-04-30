include "types.dfy"

module Host {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(numParticipants:nat, hostId: HostId)

  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat, hostId: HostId)
  {
    && c.numParticipants == participantCount
    && c.hostId == hostId
  }

  datatype Variables = Variables(
    myEpoch: nat,
    hasLock: bool
  )
  {
    ghost predicate WF(c: Constants) {
      && 0 < c.numParticipants
      && c.hostId < c.numParticipants
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall hostId: nat | hostId < |grp_c|
        :: ConstantsValidForGroup(grp_c[hostId], |grp_c|, hostId))
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
    && if c.hostId == 0 then
        && v.myEpoch == 1
        && v.hasLock 
      else 
        && v.myEpoch == 0
        && !v.hasLock
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
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendGrant(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendGrant(c: Constants, v: Variables, v': Variables, msg: Message) 
    requires v.WF(c)
  {
    && v.hasLock
    && msg == Grant(c.hostId, Successor(c.numParticipants, c.hostId), v.myEpoch + 1)
    && v' == v.(hasLock := false)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && UniqueKeyInFlightForHost(c, v, 0, msgOps.recv.value)   // the 0 literal is a useless dummy value
    && v' == v.(hasLock := true, myEpoch := msgOps.recv.value.epoch)
  }

  // Key in-flight definition
  ghost predicate UniqueKeyInFlightForHost(c: Constants, v: Variables, key: UniqueKey, msg: Message) {
    && msg.dst == c.hostId
    && v.myEpoch < msg.epoch
  }

  // Key owned by host definition
  ghost predicate HostOwnsUniqueKey(c: Constants, v: Variables, key: UniqueKey) {
    && v.hasLock
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host
