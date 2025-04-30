include "types.dfy"

module Host {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary

  datatype Constants = Constants(hostId: HostId, clusterSize: nat)

  ghost predicate ConstantsValidForGroup(c: Constants, hostId: HostId, clusterSize: nat)
  {
    && c.hostId == hostId
    && c.clusterSize == clusterSize
  }

  datatype Variables = Variables(
    receivedVotes: set<HostId>,
    nominee: MonotonicWriteOnceOption<HostId>,   // monotonic option
    isLeader: bool                      // am I the leader?
  ) {
    ghost predicate HasVoteFrom(voter: HostId) 
    {
      voter in receivedVotes
    }

    ghost predicate Nominates(h: HostId) 
    {
      nominee == WOSome(h)
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForGroup(grp_c[idx], idx, |grp_c|))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>) {
    && GroupWF(grp_c, grp_v)
    && (forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i]))
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.receivedVotes == {}
    && v.nominee == WONone
    && v.isLeader == false
  }

  datatype Step =
    NominateSelfStep() 
    | SendVoteReqStep()
    | RecvVoteReqStep() 
    | SendVoteStep()
    | RecvVoteStep()
    | VictoryStep() 
    | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case NominateSelfStep => NextHostNominateSelfStep(c, v, v', msgOps)
      case SendVoteReqStep => NextHostSendVoteReqStep(c, v, v', msgOps)
      case RecvVoteReqStep => NextHostRecvVoteReqStep(c, v, v', msgOps)
      case SendVoteStep => NextHostSendVoteStep(c, v, v', msgOps)
      case RecvVoteStep => NextHostRecvVoteStep(c, v, v', msgOps)
      case VictoryStep => NextVictoryStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == None
          && msgOps.recv == None
  }

  ghost predicate NextHostNominateSelfStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.None?
    && v.nominee.WONone?
    && v' == v.(
        nominee := WOSome(c.hostId)
      )
  }

  ghost predicate NextHostSendVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendVoteReq(c, v, v', msgOps.send.value)
  }

  /***
      sendPredicate: hosts, VoteReq
  ***/
  ghost predicate SendVoteReq(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.nominee.WOSome?
    && v.nominee.value == c.hostId
    // send message and update v'
    && msg == VoteReq(v.nominee.value)
    && v' == v
  }

  ghost predicate NextHostRecvVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && VoteReqRecvFunc(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate VoteReqRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.nominee.WONone?
    && msg.VoteReq?
    // update v'
    && v' == v.(nominee := WOSome(msg.candidate))
  }

  ghost predicate NextHostSendVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendVote(c, v, v', msgOps.send.value)
  }

  /***
      sendPredicate: hosts, Vote
  ***/
  ghost predicate SendVote(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.nominee.WOSome?
    // send message and update v'
    && msg == Vote(c.hostId, v.nominee.value)
    && v' == v
  }

  ghost predicate NextHostRecvVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && VoteRecvFunc(c, v, v', msgOps.recv.value)
  }

    // Receive predicate
  ghost predicate VoteRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.Vote?
    && msg.candidate == c.hostId
    // update v'
    && v' == v.(receivedVotes := v.receivedVotes + {msg.voter})
  }

  ghost predicate NextVictoryStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.None?
    && SetIsQuorum(c.clusterSize, v.receivedVotes)
    && v' == v.(isLeader := true)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module Hosts