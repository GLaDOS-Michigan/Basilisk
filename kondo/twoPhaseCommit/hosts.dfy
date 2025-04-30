include "types.dfy"

module CoordinatorHost {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary

  datatype Constants = Constants(numParticipants: nat)

  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat)
  {
    c.numParticipants == participantCount
  }

  datatype Variables = Variables(
    decision: MonotonicWriteOnceOption<Decision>, 
    yesVotes: set<HostId>,
    noVotes: set<HostId>
  )
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, participantCount: nat)
  {
    // There must be exactly one coordinator
    && |grp_c| == 1
    // The coordinator's constants must correctly account for the number of participants
    && ConstantsValidForGroup(grp_c[0], participantCount)
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, participantCount: nat)
  {
    && GroupWFConstants(grp_c, participantCount)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    // Coordinator is initialized to know about the N-1 participants.
    && |grp_c| == 1
    && |grp_v| == |grp_c|
    && Init(grp_c[0], grp_v[0])
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.decision.WONone?
    && v.yesVotes == {}
    && v.noVotes == {}
  }

  datatype Step =
    VoteReqStep() | ReceiveStep() | DecisionStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case VoteReqStep => NextVoteReqStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case DecisionStep => NextDecisionStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendVoteReqMsg(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendVoteReqMsg(c: Constants, v: Variables, v': Variables, msg: Message) {
    && msg == VoteReqMsg
    && v' == v 
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveVote(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveVote(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.VoteMsg?
    && var vote, src := msg.v, msg.src;
    // update v'
    && if vote == Yes then 
        v' == v.(
          yesVotes := v.yesVotes + {src}
        )
      else
        v' == v.(
          noVotes := v.noVotes + {src}
        )
  }

  // Receive vote trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveVoteTrigger1(c: Constants, v: Variables, voterId: HostId) {
    voterId in v.yesVotes
  }

    ghost predicate ReceiveVoteTrigger2(c: Constants, v: Variables, voterId: HostId) {
    voterId in v.noVotes
  }

  ghost predicate NextDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && (|v.noVotes| > 0 || |v.yesVotes| == c.numParticipants)
    && SendDecideMsg(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendDecideMsg(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.decision.WONone?
    && (|v.noVotes| > 0 || |v.yesVotes| == c.numParticipants)
    // send message and update v'
    && if |v.noVotes| > 0 then
        && v' == v.(decision := WOSome(Abort))
        && msg == DecideMsg(Abort)
    else if |v.yesVotes| == c.numParticipants then
        && v' == v.(decision := WOSome(Commit))
        && msg == DecideMsg(Commit)
    else
      false
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module CoordinatorHost


module ParticipantHost {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  ghost predicate ConstantsValidForGroup(c: Constants, hostId: HostId)
  {
    c.hostId == hostId
  }

  datatype Variables = Variables(
    // Boolean flag that acts as enabling condition for sending VoteMsg, introduced to make
    // receiving voteReq and sending vote two distinct steps.
    sendVote: bool,
    decision: MonotonicWriteOnceOption<Decision>
  )
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There must at least be a participant
    && 0 < |grp_c|
    // The participants's constants must match their group positions.
    // (Actually, they just need to be distinct from one another so we get
    // non-conflicting votes, but this is an easy way to express that property.)
    && (forall hostid:HostId | hostid < |grp_c|
        :: ConstantsValidForGroup(grp_c[hostid], hostid))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_c, grp_v)
    // Participants initted with their ids.
    && (forall hostid:HostId | hostid < |grp_c| ::
        Init(grp_c[hostid], grp_v[hostid])
      )
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sendVote == false
    && v.decision == WONone
  }

  datatype Step =
    ReceiveVoteReqStep() | ReceiveDecisionStep() | SendVoteStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveVoteReqStep => NextReceiveVoteReqStep(c, v, v', msgOps)
      case ReceiveDecisionStep => NextReceiveDecisionStep(c, v, v', msgOps)
      case SendVoteStep => NextSendVoteStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextReceiveVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && NextReceiveVoteReqStepRecvFunc(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate NextReceiveVoteReqStepRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.VoteReqMsg?
    // update v'
    && v == v'.(sendVote := true)
  }

  ghost predicate NextReceiveDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && NextReceiveDecisionStepRecvFunc(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate NextReceiveDecisionStepRecvFunc(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.DecideMsg?
    && v.decision.WONone?
    // update v'
    && v' == v.(decision := WOSome(msg.decision))
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendVoteMsg(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendVoteMsg(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.sendVote == true
    // send message
    && msg == VoteMsg(c.preference, c.hostId)
    // update v'
    && v' == v.(sendVote := false)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module ParticipantHost
