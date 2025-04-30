include "../hosts.dfy"

module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
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
    participants: seq<ParticipantHost.Variables>,
    network: Network.Variables
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
    && Network.Init(v.network)
    && CoordinatorHost.GroupInit(c.coordinator, v.coordinator)
    && ParticipantHost.GroupInit(c.participants, v.participants)
  }

  ghost predicate CoordinatorAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && CoordinatorHost.Next(c.coordinator[0], v.coordinator[0], v'.coordinator[0], msgOps)
    // all other hosts UNCHANGED
    && v'.participants == v.participants
  }

  ghost predicate ParticipantAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidParticipantId(hostid)
    && ParticipantHost.Next(c.participants[hostid], v.participants[hostid], v'.participants[hostid], msgOps)
    // all other hosts UNCHANGED
    && v'.coordinator == v.coordinator
    && (forall other:nat | c.ValidParticipantId(other) && other != hostid :: v'.participants[other] == v.participants[other])
  }

  datatype Step =
    | CoordinatorStep(msgOps: MessageOps)
    | ParticipantStep(actorIdx: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && Network.Next(v.network, v'.network, step.msgOps)
    && match step
      case CoordinatorStep(msgOps) => CoordinatorAction(c, v, v', msgOps)
      case ParticipantStep(actor, msgOps) => ParticipantAction(c, v, v', actor, msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}


