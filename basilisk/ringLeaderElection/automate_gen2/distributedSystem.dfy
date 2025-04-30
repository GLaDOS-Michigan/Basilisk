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
  import Host

  datatype Constants = Constants(hosts: seq<Host.Constants>) {
    ghost predicate ValidIdx(id: int)
      decreases this, id
    {
      0 <= id < |hosts|
    }

    ghost predicate UniqueIds()
      decreases this
    {
      forall i: int, j: int | ValidIdx(i) && ValidIdx(j) && hosts[i].hostId == hosts[j].hostId :: 
        i == j
    }

    ghost predicate WF()
      decreases this
    {
      0 < |hosts| &&
      UniqueIds()
    }
  }
  // end datatype Constants

  datatype Hosts = Hosts(hosts: seq<Host.Variables>) {
    ghost predicate WF(c: Constants)
      decreases this, c
    {
      c.WF() &&
      Host.GroupWF(c.hosts, hosts)
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
    && Host.GroupInit(c.hosts, h.hosts)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
   && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  datatype Step = 
    | HostStep(actor: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step
      case HostStep(actor, msgOps) => NextHostStep(c, h, h', actor, msgOps)
  }

  ghost predicate NextHostStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && 0 <= actor < |h.hosts|
    && Host.Next(c.hosts[actor], h.hosts[actor], h'.hosts[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall other| 0 <= other < |h.hosts| && other != actor :: h'.hosts[other] == h.hosts[other])
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
