/// This file is auto-generated
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
  import opened Types
  import opened UtilitiesLibrary
  import opened Network
  import ServerHost
  import ClientHost

  datatype Constants = Constants(clients: seq<ClientHost.Constants>, servers: seq<ServerHost.Constants>) {
    ghost predicate WF()
      decreases this
    {
      ClientHost.GroupWFConstants(clients) &&
      ServerHost.GroupWFConstants(servers)
    }

    ghost predicate ValidClientIdx(idx: nat)
      decreases this, idx
    {
      idx < |clients|
    }

    ghost function GetServer(): ServerHost.Constants
      requires WF()
      decreases this
    {
      servers[0]
    }
  }
  // end datatype Constants

  datatype Hosts = Hosts(clients: seq<ClientHost.Variables>, servers: seq<ServerHost.Variables>) {
    ghost predicate WF(c: Constants)
      decreases this, c
    {
      c.WF() &&
      ClientHost.GroupWF(c.clients, clients) &&
      ServerHost.GroupWF(c.servers, servers)
    }

    ghost function GetServer(c: Constants): ServerHost.Variables
      requires WF(c)
      decreases this, c
    {
      servers[0]
    }
  }
  // end datatype Hosts

  datatype Variables = Variables(
    history: seq<Hosts>,
    network: Network.Variables
  ) {
  
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
  
    ghost function Last() : (h: Hosts)
      requires 0 < |history|
      ensures h == history[|history|-1]
      ensures h == History(|history|-1)
   {
      UtilitiesLibrary.Last(history)
    }
  
    ghost function History(i: int) : (h: Hosts)
      requires ValidHistoryIdx(i)
      ensures h == history[i]
    {
      history[i]
    }
  }  // end datatype Variables


  ghost predicate InitHosts(c: Constants, h: Hosts)
    requires h.WF(c)
  {
    && ClientHost.GroupInit(c.clients, h.clients)
    && ServerHost.GroupInit(c.servers, h.servers)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
   && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  datatype Step = 
    | ClientHostStep(actor: nat, msgOps: MessageOps)
    | ServerHostStep(actor: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step
      case ClientHostStep(actor, msgOps) => NextClientHostStep(c, h, h', actor, msgOps)
      case ServerHostStep(actor, msgOps) => NextServerHostStep(c, h, h', actor, msgOps)
  }

  ghost predicate NextClientHostStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && 0 <= actor < |h.clients|
    && ClientHost.Next(c.clients[actor], h.clients[actor], h'.clients[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall other| 0 <= other < |h.clients| && other != actor :: h'.clients[other] == h.clients[other])
    && h'.servers == h.servers
  }

  ghost predicate NextServerHostStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && 0 <= actor < |h.servers|
    && ServerHost.Next(c.servers[actor], h.servers[actor], h'.servers[actor], msgOps)
    // all other hosts UNCHANGED
    && h'.clients == h.clients
    && (forall other| 0 <= other < |h.servers| && other != actor :: h'.servers[other] == h.servers[other])
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

  // Bundle of Variable properties
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

} // end module DistributedSystem
