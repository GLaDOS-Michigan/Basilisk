include "types.dfy"

module ClientHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(myId: HostId)

  ghost predicate ConstantsValidForGroup(c: Constants, id: HostId)
  {
    c.myId == id
  }

  datatype Variables = Variables(
    hasLock: bool,
    epoch: nat
  )
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall hostId: nat | hostId < |grp_c|
        :: ConstantsValidForGroup(grp_c[hostId], hostId))
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
    && v.hasLock == false
  }

  datatype Step =
    ReceiveStep() | ReleaseStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case ReleaseStep => NextReleaseStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
  }

  ghost predicate NextReleaseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF(c)
  {
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendRelease(c, v, v', msgOps.send.value)
  }

  ghost predicate SendRelease(c: Constants, v: Variables, v': Variables, msg: Message) 
    requires v.WF(c)
  {
    // Enabling conditions
    && v.hasLock
    // Construct message
    && msg == Release(c.myId, v.epoch + 1) // increment version
    // Update v'
    && v' == v.(hasLock := false)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && var msg := msgOps.recv.value;
    && UniqueKeyInFlightForHost(c, v, 0, msg)  // 0 is a dummy value
    && v' == v.(
      epoch := msg.epoch,
      hasLock := true
    )
  }

  // Key in-flight definition
  ghost predicate UniqueKeyInFlightForHost(c: Constants, v: Variables, key: UniqueKey, msg: Message) {
    && msg.Grant?
    && msg.dst == c.myId
    && v.epoch < msg.epoch
  }

  // Key owned by host definition
  ghost predicate HostOwnsUniqueKey(c: Constants, v: Variables, key: UniqueKey) {
    && v.hasLock
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module ClientHost


module ServerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(clientIds: set<HostId>)

  ghost predicate ConstantsValidForGroup(c: Constants, clientIds: set<HostId>)
  {
    c.clientIds == clientIds
  }

  datatype Variables = Variables(
    hasLock: bool,
    epoch: nat,
    nextClient: HostId
  )
  {
    ghost predicate WF(c: Constants) {
      nextClient in c.clientIds
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, clientIds: set<HostId>) {
    && 0 < |grp_c|
    && (forall hostId: nat | hostId < |grp_c|
        :: ConstantsValidForGroup(grp_c[hostId], clientIds))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, clientIds: set<HostId>) {
    && GroupWFConstants(grp_c, clientIds)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, clientIds: set<HostId>) {
    && GroupWF(grp_c, grp_v, clientIds)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.hasLock == true
    && v.nextClient in c.clientIds
  }

  datatype Step =
    GrantStep() | ReceiveStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case GrantStep => NextGrantStep(c, v, v', msgOps)
      case ReleaseStep => NextReceiveStep(c, v, v', msgOps)
  }

  ghost predicate NextGrantStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF(c)
  {
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendGrant(c, v, v', msgOps.send.value)
  }

  ghost predicate SendGrant(c: Constants, v: Variables, v': Variables, msg: Message) 
    requires v.WF(c)
  {
    // Enabling conditions
    && v.hasLock
    // Construct message
    && msg == Grant(0, v.nextClient, v.epoch + 1) // increment version
    // Update v'
    && v' == v.(hasLock := false, nextClient := v'.nextClient)
    && v'.nextClient in c.clientIds
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && var msg := msgOps.recv.value;
    && UniqueKeyInFlightForHost(c, v, 0, msg)
    && v' == v.(
      epoch := msg.epoch,
      hasLock := true
    )
  }

  // Key in-flight definition
  ghost predicate UniqueKeyInFlightForHost(c: Constants, v: Variables, key: UniqueKey, msg: Message) {
    && msg.Release?
    && v.epoch < msg.epoch
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