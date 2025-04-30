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
    receivedVotes: MonotonicSet<HostId>,
    nominee: MonotonicWriteOnceOption<HostId>,   // monotonic option
    isLeader: MonotonicBool                      // am I the leader?
  ) {
    ghost predicate HasVoteFrom(voter: HostId) 
    {
      receivedVotes.Contains(voter)
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
    && v.receivedVotes == MonotonicSet({})
    && v.nominee == WONone
    && v.isLeader == MonotonicBool(false)
  }

  datatype Step =
    | SendVoteReqStep()
    | RecvVoteReqStep() 
    | RecvVoteStep()
    | VictoryStep() 
    | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case SendVoteReqStep => NextHostSendVoteReqStep(c, v, v', msgOps)
      case RecvVoteReqStep => NextHostRecvVoteReqStep(c, v, v', msgOps)
      case RecvVoteStep => NextHostRecvVoteStep(c, v, v', msgOps)
      case VictoryStep => NextVictoryStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == None
          && msgOps.recv == None
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
    && v.nominee.WONone?
    // send message and update v'
    && msg == VoteReq(c.hostId)
    && v' == v
  }

  ghost predicate NextHostRecvVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.Some?
    && ReceiveVoteReqSendVote(c, v, v', msgOps.recv.value, msgOps.send.value)
  }

  // Receive-and-Send predicate
  ghost predicate ReceiveVoteReqSendVote(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
    // enabling conditions
    && v.nominee.WONone?
    && inMsg.VoteReq?
    // update v' and specify outMsg
    && outMsg == Vote(c.hostId, inMsg.candidate)
    && v' == v.(nominee := WOSome(inMsg.candidate))
  }

  // Receive predicate trigger
  ghost predicate ReceiveVoteReqTrigger(c: Constants, v: Variables, candidate: HostId) {
    && v.nominee == WOSome(candidate)
  }

  ghost predicate NextHostRecvVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveVote(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveVote(c: Constants, v: Variables, v': Variables, inMsg: Message) {
    // enabling conditions
    && inMsg.Vote?
    && inMsg.candidate == c.hostId
    // update v'
    && v' == v.(receivedVotes := v.receivedVotes.Add(inMsg.voter))
  }

  // Receive predicate trigger
  // First 2 arguments are mandatory. Third argument identifies voter. 
  ghost predicate ReceiveVoteTrigger(c: Constants, v: Variables, voter: HostId) {
    && v.receivedVotes.Contains(voter)
  }

  ghost predicate NextVictoryStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.None?
    && SetIsQuorum(c.clusterSize, v.receivedVotes.Value())
    && v' == v.(isLeader := MonotonicBool(true))
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module Hosts