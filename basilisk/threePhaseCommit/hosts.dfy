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
    yesVotes: MonotonicSet<HostId>,
    noVotes: MonotonicSet<HostId>,
    preCommitAcks: MonotonicSet<HostId>
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
    && v.yesVotes == MonotonicSet({})
    && v.noVotes == MonotonicSet({})
    && v.preCommitAcks == MonotonicSet({})
  }

  datatype Step =
    VoteReqStep() | ReceiveVoteStep() | DecisionStep() | StutterStep() | PreCommitStep() | ReceivePrecommitStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case VoteReqStep => NextVoteReqStep(c, v, v', msgOps)
      case ReceiveVoteStep => NextReceiveVoteStep(c, v, v', msgOps)
      case DecisionStep => NextDecisionStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
      case PreCommitStep => NextSendPrecommitStep(c, v, v', msgOps)
      case ReceivePrecommitStep => NextRecvPrecommitAckStep(c, v, v', msgOps)
  }

  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendVoteReq(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendVoteReq(c: Constants, v: Variables, v': Variables, msg: Message) {
    && msg == VoteReq
    && v' == v 
  }

  ghost predicate NextReceiveVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && (ReceiveVoteYes(c, v, v', msgOps.recv.value) || ReceiveVoteNo(c, v, v', msgOps.recv.value))
  }

  // Receive predicate
  ghost predicate ReceiveVoteNo(c: Constants, v: Variables, v': Variables, inMsg: Message) {
    // enabling conditions
    && inMsg.Vote?
    && var vote, src := inMsg.v, inMsg.src;
    && vote == No
    // update v'
    && v' == v.(
        noVotes := v.noVotes.Add(src)
      )
  }

  // Receive predicate
  ghost predicate ReceiveVoteYes(c: Constants, v: Variables, v': Variables, inMsg: Message) {
    // enabling conditions
    && inMsg.Vote?
    && var vote, src := inMsg.v, inMsg.src;
    && vote == Yes
    // update v'
    && v' == v.(
      yesVotes := v.yesVotes.Add(src)
    )
  }

  // Receive vote trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveVoteTrigger1(c: Constants, v: Variables, voterId: HostId) {
    v.yesVotes.Contains(voterId)
  }

  ghost predicate ReceiveVoteTrigger2(c: Constants, v: Variables, voterId: HostId) {
    v.noVotes.Contains(voterId)
  }

  ghost predicate NextDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && (|v.noVotes.s| > 0 || |v.preCommitAcks.s| == c.numParticipants)
    && SendDecide(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendDecide(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.decision.WONone?
    && (|v.noVotes.s| > 0 || |v.preCommitAcks.s| == c.numParticipants)
    // send message and update v'
    && if |v.noVotes.s| > 0 then
        && v' == v.(decision := WOSome(Abort))
        && msg == Decide(Abort)
    else if |v.preCommitAcks.s| == c.numParticipants then
        && v' == v.(decision := WOSome(Commit))
        && msg == Decide(Commit)
    else
      false
  }

  ghost predicate NextSendPrecommitStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps){
    && msgOps.recv.None?
    && msgOps.send.Some?
    && |v.yesVotes.s| == c.numParticipants
    && SendPrecommit(c, v, v', msgOps.send.value)
  }
  ghost predicate SendPrecommit(c: Constants, v: Variables, v': Variables, msg: Message){
    && msg.Precommit?
    && v' == v
    && |v.yesVotes.s| == c.numParticipants
  }
  ghost predicate NextRecvPrecommitAckStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps){
    && msgOps.send.None?
    && msgOps.recv.Some?
    && RecvPrecommitAck(c, v, v', msgOps.recv.value)
  }

   ghost predicate RecvPrecommitAck(c: Constants, v: Variables, v': Variables, inMsg: Message){
    && inMsg.Precommitack?
    && var src := inMsg.src;
    // update v'
    && v' == v.(preCommitAcks := v.preCommitAcks.Add(src))
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
    decision: MonotonicWriteOnceOption<Decision>,
    precommited: MonotonicBool
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
    && v.decision == WONone
    && !v.precommited.b
  }

  datatype Step =
    ReceiveVoteReqStep() | ReceiveDecisionStep() | StutterStep() | ReceivePrecommitStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveVoteReqStep => NextReceiveVoteReqStep(c, v, v', msgOps)
      case ReceiveDecisionStep => NextReceiveDecisionStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
      case ReceivePrecommitStep => NextReceivePrecommitSendPrecommitackStep(c, v, v', msgOps)
  }

  ghost predicate NextReceiveVoteReqStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.Some?
    && msgOps.recv.Some?
    && ReceiveVoteReqSendVote(c, v, v', msgOps.recv.value, msgOps.send.value)
  }

  // Receive-Send predicate
  ghost predicate ReceiveVoteReqSendVote(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
    // enabling conditions
    && inMsg.VoteReq?
    // update v' and specify outMsg
    && outMsg == Vote(c.preference, c.hostId)
    && v == v'
  }

  ghost predicate NextReceiveDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveDecide(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveDecide(c: Constants, v: Variables, v': Variables, inMsg: Message) {
    // enabling conditions
    && inMsg.Decide?
    && v.decision.WONone?
    // update v'
    && v' == v.(decision := WOSome(inMsg.decision))
  }

  ghost predicate NextReceivePrecommitSendPrecommitackStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps){
    && msgOps.send.Some?
    && msgOps.recv.Some?
    && ReceivePrecommitSendPrecommitack(c, v, v', msgOps.recv.value, msgOps.send.value)

  }
  ghost predicate ReceivePrecommitSendPrecommitack(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message)
  {
    && outMsg == Precommitack(c.hostId)
    && inMsg.Precommit?
    && v' == v.(precommited := MonotonicBool(true))
  }

  // Receive decision trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveDecideTrigger(c: Constants, v: Variables) {
    v.decision.WOSome?
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module ParticipantHost
