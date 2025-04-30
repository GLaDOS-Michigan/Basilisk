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
    decision: Option<Decision>, 
    yesVotes: MonotonicSet<HostId>,
    noVotes: MonotonicSet<HostId>
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
    && v.decision.None?
    && v.yesVotes == MonotonicSet({})
    && v.noVotes == MonotonicSet({})
  }

  datatype Step =
    ReceiveStep() | DecisionStep() | SendDecisionStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case DecisionStep => MakeDecision(c, v, v', msgOps)
      case SendDecisionStep => NextSendDecisionStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
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

  ghost predicate MakeDecision(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.None?
    && msgOps.recv.None?
    && v.decision.None?
    && if |v.noVotes.s| > 0 then
          v' == v.(decision := Some(Abort))
        else if |v.yesVotes.s| == c.numParticipants then
          v' == v.(decision := Some(Commit))
        else
          v' == v
  }

  ghost predicate NextSendDecisionStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendDecide(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendDecide(c: Constants, v: Variables, v': Variables, outMsg: Message) {
    // enabling conditions
    && v.decision.Some?
    && v' == v
    && outMsg == Decide(v.decision.value)
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
    decision: Option<Decision>
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
    v.decision == None
  }

  datatype Step =
    SendVoteStep() | ReceiveDecisionStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case SendVoteStep => NextSendVoteStep(c, v, v', msgOps)
      case ReceiveDecisionStep => NextReceiveDecisionStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextSendVoteStep (c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendVote(c, v, v', msgOps.send.value)
  }

  // Receive-Send predicate
  ghost predicate SendVote(c: Constants, v: Variables, v': Variables, outMsg: Message) {
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
    && v.decision.None?
    // update v'
    && v' == v.(decision := Some(inMsg.decision))
  }

  // Receive decision trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveDecideTrigger(c: Constants, v: Variables) {
    v.decision.Some?
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
} // end module ParticipantHost
