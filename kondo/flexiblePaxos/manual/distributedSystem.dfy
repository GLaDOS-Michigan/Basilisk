include "hosts.dfy"

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
  import opened Types
  import opened Network
  import LeaderHost
  import AcceptorHost
  import LearnerHost

  datatype Constants = Constants(
    p1Quorum: nat, 
    p2Quorum: nat, 
    n: nat,
    leaderConstants: seq<LeaderHost.Constants>,
    acceptorConstants: seq<AcceptorHost.Constants>,
    learnerConstants: seq<LearnerHost.Constants>)
  {
    ghost predicate WF() {
      && p1Quorum + p2Quorum == n + 1
      && UniqueIds()
    }

    ghost predicate UniqueIds() {
      && UniqueLeaderIds()
      && UniqueAcceptorIds()
      && UniqueLearnerIds()
    }

    ghost predicate ValidLeaderIdx(id: int) {
      0 <= id < |leaderConstants|
    }

    ghost predicate ValidAcceptorIdx(id: int) {
      0 <= id < |acceptorConstants|
    }

    ghost predicate ValidLearnerIdx(id: int) {
      0 <= id < |learnerConstants|
    }
    
    ghost predicate UniqueLeaderIds() {
      forall i, j | ValidLeaderIdx(i) && ValidLeaderIdx(j) && leaderConstants[i].id == leaderConstants[j].id :: i == j
    }

    ghost predicate UniqueAcceptorIds() {
      forall i, j | ValidAcceptorIdx(i) && ValidAcceptorIdx(j) && acceptorConstants[i].id == acceptorConstants[j].id :: i == j
    }

    ghost predicate UniqueLearnerIds() {
      forall i, j | ValidLearnerIdx(i) && ValidLearnerIdx(j) && learnerConstants[i].id == learnerConstants[j].id :: i == j
    }
  }

  datatype Variables = Variables(
    leaders: seq<LeaderHost.Variables>,
    acceptors: seq<AcceptorHost.Variables>,
    learners: seq<LearnerHost.Variables>,
    network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && LeaderHost.GroupWF(c.leaderConstants, leaders, c.p1Quorum)
      && AcceptorHost.GroupWF(c.acceptorConstants, acceptors, c.n)
      && LearnerHost.GroupWF(c.learnerConstants, learners, c.p2Quorum)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && LeaderHost.GroupInit(c.leaderConstants, v.leaders, c.p1Quorum)
    && AcceptorHost.GroupInit(c.acceptorConstants, v.acceptors, c.n)
    && LearnerHost.GroupInit(c.learnerConstants, v.learners, c.p2Quorum)

    && Network.Init(v.network)
  }
  
  datatype Step = 
    LeaderStep(actor: nat, msgOps: MessageOps)
    | AcceptorStep(actor: nat, msgOps: MessageOps)
    | LearnerStep(actor: nat, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
  {
    && Network.Next(v.network, v'.network, step.msgOps)
    && match step 
      case LeaderStep(actor, msgOps) => NextLeaderStep(c, v, v', actor, msgOps)
      case AcceptorStep(actor, msgOps) => NextAcceptorStep(c, v, v', actor, msgOps)
      case LearnerStep(actor, msgOps) => NextLearnerStep(c, v, v', actor, msgOps)
  }

  ghost predicate NextLeaderStep(c: Constants, v: Variables, v': Variables, actor: nat, msgOps: MessageOps) 
    requires v.WF(c) && v'.WF(c)
  {
    && c.ValidLeaderIdx(actor)
    && LeaderHost.Next(c.leaderConstants[actor], v.leaders[actor], v'.leaders[actor], msgOps)
    // all other hosts UNCHANGED
    && (forall other| c.ValidLeaderIdx(other) && other != actor :: v'.leaders[other] == v.leaders[other])
    && v'.acceptors == v.acceptors
    && v'.learners == v.learners
  }

  ghost predicate NextAcceptorStep(c: Constants, v: Variables, v': Variables, actor: nat, msgOps: MessageOps) 
    requires v.WF(c) && v'.WF(c)
  {
    && c.ValidAcceptorIdx(actor)
    && AcceptorHost.Next(c.acceptorConstants[actor], v.acceptors[actor], v'.acceptors[actor], msgOps)
    // all other hosts UNCHANGED
    && v'.leaders == v.leaders
    && (forall other| c.ValidAcceptorIdx(other) && other != actor :: v'.acceptors[other] == v.acceptors[other])
    && v'.learners == v.learners
  }

  ghost predicate NextLearnerStep(c: Constants, v: Variables, v': Variables, actor: nat, msgOps: MessageOps) 
    requires v.WF(c) && v'.WF(c)
  {
    && c.ValidLearnerIdx(actor)
    && LearnerHost.Next(c.learnerConstants[actor], v.learners[actor], v'.learners[actor], msgOps)
    // all other hosts UNCHANGED
    && v'.leaders == v.leaders
    && v'.acceptors == v.acceptors
    && (forall other| c.ValidLearnerIdx(other) && other != actor :: v'.learners[other] == v.learners[other])
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }
}  // end module DistributedSystem