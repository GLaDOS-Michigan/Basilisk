include "types.dfy"

module Host {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(myId: HostId, hostIds: set<HostId>)

  ghost predicate ConstantsValidForGroup(c: Constants, id: HostId, hostIds: set<HostId>)
  {
    && c.myId == id
    && c.hostIds == hostIds
  }

  datatype Variables = Variables(
    myKeys: map<UniqueKey, Entry>,   // is the key live, and the version number
    nextKeyToSend: UniqueKey,        // next key to transfer to dest
    nextDst: HostId
  )
  {
    ghost predicate WF(c: Constants) {
      && c.myId in c.hostIds
    }

    ghost predicate HasKey(k: UniqueKey) {
      && k in myKeys
    }

    ghost predicate HasLiveKey(k: UniqueKey) {
      && k in myKeys
      && myKeys[k].live
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && var allHosts := (set x | 0 <= x < |grp_c|);
    && (forall hostId: nat | hostId < |grp_c|
        :: ConstantsValidForGroup(grp_c[hostId], hostId, allHosts))
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
    // Hosts have disjoint live keys
    && (forall k: UniqueKey, i, j | 
          && 0 <= i < |grp_c|
          && 0 <= j < |grp_c|
          && grp_v[i].HasLiveKey(k) 
          && grp_v[j].HasLiveKey(k) 
        :: i == j)
    // Each host have every key
    && (forall k: UniqueKey, i: HostId | 0 <= i < |grp_c| ::
          grp_v[i].HasKey(k))
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && 0 < |v.myKeys|
    && (forall k | k in v.myKeys :: v.myKeys[k].version == 0)
    && v.HasLiveKey(v.nextKeyToSend)
    && v.nextDst in c.hostIds
  }

  datatype Step =
    SendStep() | ReceiveStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    && v.WF(c)
    && match step
      case SendStep => NextSendStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
  }

  ghost predicate NextSendStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
    requires v.WF(c)
  {
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendReconf(c, v, v', msgOps.send.value)
  }

  ghost predicate SendReconf(c: Constants, v: Variables, v': Variables, msg: Message) 
    requires v.WF(c)
  {
    // Enabling conditions
    && 0 < |v.myKeys| 
    && HostOwnsUniqueKey(c, v, v.nextKeyToSend)
    && v.nextDst in c.hostIds
    // Construct message
    && msg == Reconf(c.myId, v.nextDst, v.nextKeyToSend, v.myKeys[v.nextKeyToSend].version+1) // increment version
    // Update v'
    && v'.myKeys == 
        (map k | k in v.myKeys
          :: if k != v.nextKeyToSend then v.myKeys[k] else Entry(false, v.myKeys[k].version))
    && v'.nextDst in c.hostIds
    && v'.HasLiveKey(v'.nextKeyToSend)
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveReconf(c, v, v', msgOps.recv.value)
  }

  ghost predicate ReceiveReconf(c: Constants, v: Variables, v': Variables, inMsg: Message) {
    && UniqueKeyInFlightForHost(c, v, inMsg.key, inMsg)
    && v' == v.(
      myKeys := v.myKeys[inMsg.key := Entry(true, inMsg.version)]
    )
  }

  // Key in-flight definition
  ghost predicate UniqueKeyInFlightForHost(c: Constants, v: Variables, key: UniqueKey, msg: Message) {
    && msg.dst == c.myId
    && key in v.myKeys
    && key == msg.key
    && v.myKeys[key].version < msg.version
  }

  // Key owned by host definition
  ghost predicate HostOwnsUniqueKey(c: Constants, v: Variables, key: UniqueKey) {
    && v.HasLiveKey(key)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module Host
