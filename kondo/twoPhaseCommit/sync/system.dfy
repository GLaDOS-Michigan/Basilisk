include "../hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(
    coordinator: seq<CoordinatorHost.Constants>,
    participants: seq<ParticipantHost.Constants>)
  {
    ghost predicate WF() {
      && CoordinatorHost.GroupWFConstants(coordinator, |participants|)
      && ParticipantHost.GroupWFConstants(participants)
    }

    ghost predicate ValidParticipantId(id: HostId) {
      id < |participants|
    }

    ghost function GetCoordinator() : CoordinatorHost.Constants 
      requires WF()
    {
      coordinator[0]
    }
  }

  datatype Variables = Variables(
    coordinator: seq<CoordinatorHost.Variables>,
    participants: seq<ParticipantHost.Variables>
  )
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && CoordinatorHost.GroupWF(c.coordinator, coordinator, |c.participants|)
      && ParticipantHost.GroupWF(c.participants, participants)
    }

    ghost function GetCoordinator(c: Constants) : CoordinatorHost.Variables 
      requires WF(c)
    {
      coordinator[0]
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && CoordinatorHost.GroupInit(c.coordinator, v.coordinator)
    && ParticipantHost.GroupInit(c.participants, v.participants)
  }

  datatype Step =
    | VoteReqStep(participant: HostId, transmit: Transmit)
    | SendVoteStep(participant: HostId, transmit: Transmit)
    | DecideStep(transmit: Transmit)
    | StutterStep()

    
  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, participant: HostId, transmit: Transmit) 
    requires v.WF(c) && v'.WF(c)
  {
    // Coordinator action
    && transmit.m.VoteReqMsg?
    && CoordinatorHost.Next(c.GetCoordinator(), v.GetCoordinator(c), v'.GetCoordinator(c), transmit.Send())
    // Participant action
    && c.ValidParticipantId(participant)
    && ParticipantHost.Next(c.participants[participant], v.participants[participant], v'.participants[participant], transmit.Recv())
    // All others unchanged
    && (forall x:nat | c.ValidParticipantId(x) && x!= participant
        ::  v.participants[x] == v'.participants[x])
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, pidx: HostId, transmit: Transmit) 
    requires v.WF(c) && v'.WF(c)
  {
    // Participant action
    && c.ValidParticipantId(pidx)
    && transmit.m.VoteMsg?
    && ParticipantHost.Next(c.participants[pidx], v.participants[pidx], v'.participants[pidx], transmit.Send())
    // Coordinator action
    && CoordinatorHost.Next(c.GetCoordinator(), v.GetCoordinator(c), v'.GetCoordinator(c), transmit.Recv())
    // All others unchanged
    && (forall x:HostId | c.ValidParticipantId(x) && x!= pidx
        ::  v.participants[x] == v'.participants[x])
  }

  ghost predicate NextDecideStep(c: Constants, v: Variables, v': Variables, transmit: Transmit)
    requires v.WF(c) && v'.WF(c)
  {
    // Coordinator action
    && transmit.m.DecideMsg?
    && CoordinatorHost.Next(c.GetCoordinator(), v.GetCoordinator(c), v'.GetCoordinator(c), transmit.Send())
    // All others unchanged
    && (forall x:nat | c.ValidParticipantId(x)
        :: ParticipantHost.Next(c.participants[x], v.participants[x], v'.participants[x], transmit.Recv()))
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
  {
    match step
      case VoteReqStep(pidx, transmit) => NextVoteReqStep(c, v, v', pidx, transmit)
      case SendVoteStep(pidx, transmit) => NextSendVoteStep(c, v, v', pidx, transmit)
      case DecideStep(transmit) => NextDecideStep(c, v, v', transmit)
      case StutterStep => v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }
}


