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
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
} // end module Network


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import ClientHost
  import ServerHost

  datatype Constants = Constants(
    clients: seq<ClientHost.Constants>,
    server: seq<ServerHost.Constants>
    )
  {
    ghost predicate ValidClientIdx(id: int) {
      0 <= id < |clients|
    }

    ghost predicate UniqueIds() {
      forall i, j | ValidClientIdx(i) && ValidClientIdx(j) && clients[i].myId == clients[j].myId :: i == j
    }

    ghost predicate WF() {
      && 0 < |clients|
      && UniqueIds()
      && |server| == 1
    }
  }

  datatype Variables = Variables(
    clients: seq<ClientHost.Variables>,
    server: seq<ServerHost.Variables>,
    network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && ClientHost.GroupWF(c.clients, clients)
      && var allClients := (set x | 0 <= x < |c.clients| :: c.clients[x].myId);
      && ServerHost.GroupWF(c.server, server, allClients)
    }
  } // end datatype Variables

  ghost predicate InitHosts(c: Constants, v: Variables)
  {
    && var allClients := (set x | 0 <= x < |c.clients| :: c.clients[x].myId);
    && ClientHost.GroupInit(c.clients, v.clients)
    && ServerHost.GroupInit(c.server, v.server, allClients)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && InitHosts(c, v)
    && Network.Init(v.network)
  }

  ghost predicate NextClientStep(c: Constants, v: Variables, v': Variables, actor: int, msgOps: MessageOps)
    requires v.WF(c) && v'.WF(c)
  {
    && c.ValidClientIdx(actor)
    && ClientHost.Next(c.clients[actor], v.clients[actor], v'.clients[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall otherClientIdx | c.ValidClientIdx(otherClientIdx) && otherClientIdx != actor :: v'.clients[otherClientIdx] == v.clients[otherClientIdx])
    && v'.server == v.server
  }

  ghost predicate NextServerStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    requires v.WF(c) && v'.WF(c)
  {
    && ServerHost.Next(c.server[0], v.server[0], v'.server[0], msgOps)
    // all other hosts UNCHANGED
    && v'.clients == v.clients
    && |v'.server| == 1
  }

  datatype Step = 
    | ServerStep(msgOps: MessageOps)
    | ClientStep(actor: int, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
  {
    && Network.Next(v.network, v'.network, step.msgOps)
    && match step 
      case ClientStep(actor, msgOps) => NextClientStep(c, v, v', actor, msgOps)
      case ServerStep(msgOps) => NextServerStep(c, v, v', msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }
}  // end module DistributedSystem