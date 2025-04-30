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
  import LeaderHost
  import AcceptorHost
  import LearnerHost

  datatype Constants = Constants(f: nat, leaders: seq<LeaderHost.Constants>, acceptors: seq<AcceptorHost.Constants>, learners: seq<LearnerHost.Constants>) {
    ghost predicate WF()
      decreases this
    {
      0 < f &&
      UniqueIds()
    }

    ghost predicate UniqueIds()
      decreases this
    {
      UniqueLeaderIds() &&
      UniqueAcceptorIds() &&
      UniqueLearnerIds()
    }

    ghost predicate ValidLeaderIdx(id: int)
      decreases this, id
    {
      0 <= id < |leaders|
    }

    ghost predicate ValidAcceptorIdx(id: int)
      decreases this, id
    {
      0 <= id < |acceptors|
    }

    ghost predicate ValidLearnerIdx(id: int)
      decreases this, id
    {
      0 <= id < |learners|
    }

    ghost predicate UniqueLeaderIds()
      decreases this
    {
      forall i: int, j: int | ValidLeaderIdx(i) && ValidLeaderIdx(j) && leaders[i].id == leaders[j].id :: 
        i == j
    }

    ghost predicate UniqueAcceptorIds()
      decreases this
    {
      forall i: int, j: int | ValidAcceptorIdx(i) && ValidAcceptorIdx(j) && acceptors[i].id == acceptors[j].id :: 
        i == j
    }

    ghost predicate UniqueLearnerIds()
      decreases this
    {
      forall i: int, j: int | ValidLearnerIdx(i) && ValidLearnerIdx(j) && learners[i].id == learners[j].id :: 
        i == j
    }
  }
  // end datatype Constants

  datatype Hosts = Hosts(leaders: seq<LeaderHost.Variables>, acceptors: seq<AcceptorHost.Variables>, learners: seq<LearnerHost.Variables>) {
    ghost predicate WF(c: Constants)
      decreases this, c
    {
      c.WF() &&
      LeaderHost.GroupWF(c.leaders, leaders, c.f) &&
      AcceptorHost.GroupWF(c.acceptors, acceptors, c.f) &&
      LearnerHost.GroupWF(c.learners, learners, c.f)
    }

    ghost predicate LeaderCanPropose(c: Constants, ldr: LeaderId)
      requires WF(c)
      requires c.ValidLeaderIdx(ldr)
      decreases this, c, ldr
    {
      leaders[ldr].CanPropose(c.leaders[ldr])
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
      && History(0).WF(c)   // useful fact
      && (forall i | ValidHistoryIdx(i) :: History(i).WF(c))
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
    && LeaderHost.GroupInit(c.leaders, h.leaders, c.f)
    && AcceptorHost.GroupInit(c.acceptors, h.acceptors, c.f)
    && LearnerHost.GroupInit(c.learners, h.learners, c.f)
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
   && |v.history| == 1
    && InitHosts(c, v.History(0))
    && Network.Init(v.network)
  }

  datatype Step = 
    | LeaderHostStep(actor: nat, msgOps: MessageOps)
    | AcceptorHostStep(actor: nat, msgOps: MessageOps)
    | LearnerHostStep(actor: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, h: Hosts, h': Hosts, n: Network.Variables, n': Network.Variables, step: Step)
    requires h.WF(c) && h'.WF(c)
  {
    && Network.Next(n, n', step.msgOps)
    && match step
      case LeaderHostStep(actor, msgOps) => NextLeaderHostStep(c, h, h', actor, msgOps)
      case AcceptorHostStep(actor, msgOps) => NextAcceptorHostStep(c, h, h', actor, msgOps)
      case LearnerHostStep(actor, msgOps) => NextLearnerHostStep(c, h, h', actor, msgOps)
  }

  ghost predicate NextLeaderHostStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && 0 <= actor < |h.leaders|
    && LeaderHost.Next(c.leaders[actor], h.leaders[actor], h'.leaders[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall other| 0 <= other < |h.leaders| && other != actor :: h'.leaders[other] == h.leaders[other])
    && h'.acceptors == h.acceptors
    && h'.learners == h.learners
  }

  ghost predicate NextAcceptorHostStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && 0 <= actor < |h.acceptors|
    && AcceptorHost.Next(c.acceptors[actor], h.acceptors[actor], h'.acceptors[actor], msgOps)
    // all other hosts UNCHANGED
    && h'.leaders == h.leaders
    && (forall other| 0 <= other < |h.acceptors| && other != actor :: h'.acceptors[other] == h.acceptors[other])
    && h'.learners == h.learners
  }

  ghost predicate NextLearnerHostStep(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)
    requires h.WF(c) && h'.WF(c)
  {
    && 0 <= actor < |h.learners|
    && LearnerHost.Next(c.learners[actor], h.learners[actor], h'.learners[actor], msgOps)
    // all other hosts UNCHANGED
    && h'.leaders == h.leaders
    && h'.acceptors == h.acceptors
    && (forall other| 0 <= other < |h.learners| && other != actor :: h'.learners[other] == h.learners[other])
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