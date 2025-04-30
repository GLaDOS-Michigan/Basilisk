include "../hosts.dfy"

module Network {
  import opened Types

  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables) {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}  // end module Network


module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import ServerHost
  import ClientHost

  datatype Constants = Constants(
    clients: seq<ClientHost.Constants>,
    servers: seq<ServerHost.Constants>)
  {
    ghost predicate WF() {
      && ClientHost.GroupWFConstants(clients)
      && ServerHost.GroupWFConstants(servers)
    }
    
    ghost predicate ValidClientIdx(idx: nat) {
      idx < |clients|
    }

    ghost function GetServer() : ServerHost.Constants 
      requires WF()
    {
      servers[0]
    }
  }

  datatype Variables = Variables(
    clients: seq<ClientHost.Variables>,
    servers: seq<ServerHost.Variables>,
    network: Network.Variables
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && ClientHost.GroupWF(c.clients, clients)
      && ServerHost.GroupWF(c.servers, servers)
    }

    ghost function GetServer(c: Constants) : ServerHost.Variables 
      requires WF(c)
    {
      servers[0]
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Network.Init(v.network)
    && ClientHost.GroupInit(c.clients, v.clients)
    && ServerHost.GroupInit(c.servers, v.servers)
  }

  ghost predicate ClientAction(c: Constants, v: Variables, v': Variables, clientIdx: nat, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidClientIdx(clientIdx)
    && ClientHost.Next(c.clients[clientIdx], v.clients[clientIdx], v'.clients[clientIdx], msgOps)
    // all other hosts UNCHANGED
    && (forall otherIdx:nat | c.ValidClientIdx(otherIdx) && otherIdx != clientIdx :: v'.clients[otherIdx] == v.clients[otherIdx])
    && v.servers == v'.servers
  }

  ghost predicate ServerAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && ServerHost.Next(c.GetServer(), v.GetServer(c), v'.GetServer(c), msgOps)
    // all other hosts UNCHANGED
    && v.clients == v'.clients
  }

  datatype Step =
    | ClientStep(actorIdx: nat, msgOps: MessageOps)
    | ServerStep(msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && Network.Next(v.network, v'.network, step.msgOps)
    && match step
      case ClientStep(actor, msgOps) => ClientAction(c, v, v', actor, msgOps)
      case ServerStep(msgOps) => ServerAction(c, v, v', msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}  // end module Distributed System
