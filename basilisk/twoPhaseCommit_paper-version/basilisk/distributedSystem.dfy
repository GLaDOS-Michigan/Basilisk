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

  datatype Hosts = Hosts(
    coordinator: seq<CoordinatorHost.Variables>,
    participants: seq<ParticipantHost.Variables>
  ) {
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

  datatype Variables = Variables(
    history: seq<Hosts>,
    network: Network.Variables)
  {
    ghost predicate ValidHistoryIdx(i: int) {
      0 <= i < |history|
    }
    
    ghost predicate ValidHistoryIdxStrict(i: int) {
      0 <= i < |history|-1
    }

    ghost predicate WF(c: Constants) {
      && c.WF()
      && 0 < |history|
      && (forall i | ValidHistoryIdx(i) :: history[i].WF(c))
    }

    ghost function History(i: int) : (h: Hosts)
      requires ValidHistoryIdx(i)
      ensures h == history[i]
    {
      history[i]
    }

    ghost function Last() : (h: Hosts) 
      requires 0 < |history|
      ensures h == history[|history|-1]
    {
      UtilitiesLibrary.Last(history)
    }
  } // end datatype Variables

  ghost predicate InitHosts(c: Constants, h: Hosts)
  {
    && CoordinatorHost.GroupInit(c.coordinator, h.coordinator)
    && ParticipantHost.GroupInit(c.participants, h.participants)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  ghost predicate CoordinatorAction(c: Constants, h: Hosts, h': Hosts, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && CoordinatorHost.Next(c.coordinator[0], h.coordinator[0], h'.coordinator[0], msgOps)
    // all other hosts UNCHANGED
    && h'.participants == h.participants
  }

  ghost predicate ParticipantAction(c: Constants, h: Hosts, h': Hosts, hostid: HostId, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && c.ValidParticipantId(hostid)
    && ParticipantHost.Next(c.participants[hostid], h.participants[hostid], h'.participants[hostid], msgOps)
    // all other hosts UNCHANGED
    && h'.coordinator == h.coordinator
    && (forall other:nat | c.ValidParticipantId(other) && other != hostid :: h'.participants[other] == h.participants[other])
  }

  datatype Step =
    | CoordinatorStep(msgOps: MessageOps)
    | ParticipantStep(actorIdx: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step
      case CoordinatorStep(msgOps) => CoordinatorAction(c, h, h', msgOps)
      case ParticipantStep(actor, msgOps) => ParticipantAction(c, h, h', actor, msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && IsSeqExtension(v.history, v'.history)
    && exists step :: NextStep(c, v.Last(), v'.Last(), v.network, v'.network, step)
  }

/***************************************************************************************
*                                Variable properties                                   *
***************************************************************************************/

  ghost predicate {:opaque} ValidHistory(c: Constants, v: Variables)
    requires v.WF(c)
  {
    InitHosts(c, v.History(0))
  }

  ghost predicate ValidVariables(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    && ValidHistory(c, v)
  }

  lemma InitImpliesValidVariables(c: Constants, v: Variables)
    requires Init(c, v)
    ensures ValidHistory(c, v)
  {
    reveal_ValidHistory();
  }


  lemma InvNextValidVariables(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires ValidHistory(c, v)
    requires Next(c, v, v')
    ensures ValidHistory(c, v')
  {
    reveal_ValidHistory();
    VariableNextProperties(c, v, v');
  }

  lemma VariableNextProperties(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires Next(c, v, v')
    ensures 1 < |v'.history|
    ensures |v.history| == |v'.history| - 1
    ensures v.Last() == v.History(|v'.history|-2) == v'.History(|v'.history|-2)
    ensures forall i | 0 <= i < |v'.history|-1 :: v.History(i) == v'.History(i)
  {
    assert 0 < |v.history|;
    assert 1 < |v'.history|;
  }
} // end module Distributed System


