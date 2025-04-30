include "../lib/MonotonicityLibrary.dfy"
include "types.dfy"

module Host {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary

  datatype Step = InitCandidacyStep | SendVoteStep | RecvVoteStep | BecomeLeaderStep | LearnLeaderNewTermStep | LearnLeaderSameTermStep
  datatype Status = Leader | Candidate | Follower

  datatype MonotonicTermState = MonotonicTermState(term:nat, acceptors: set<nat>, votedFor: nat){
    ghost predicate SatisfiesMonotonic(other: MonotonicTermState){
      && other.term <= term
      && (other.term == term ==> (other.acceptors <= acceptors && other.votedFor == votedFor))
    }
  }
  
  datatype Constants = Constants(idx: nat, f: nat)
    
  datatype Variables = Variables(
    status: Status,
    ms: MonotonicTermState
  )
  {
    ghost predicate WF(c: Constants){
      && (!(status.Follower?) ==> ms.votedFor == c.idx && c.idx in ms.acceptors)
    }
  }


  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f:nat)
  {
    && (|grp_c| > 1)
    && (|grp_c| == |grp_v| == 2*f+1)
    && (forall idx | 0 <= idx < |grp_c| :: 
      && (grp_c[idx].idx == idx && grp_c[idx].f == f)
      && (grp_v[idx].WF(grp_c[idx])))
  }
  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f:nat)
  {
    && (GroupWF(grp_c, grp_v, f))
    && (forall idx | 0 <= idx < |grp_v| :: 
      && (grp_v[idx].status.Follower?)
      && (grp_v[idx].ms.term == 0)
      && (grp_v[idx].ms.acceptors == {idx})
      && (grp_v[idx].ms.votedFor == idx))
  }

  ghost predicate NextInitCandidacyStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendVoteReq(c, v, v', msgOps.send.value)
  }

  ghost predicate SendVoteReq(c: Constants, v: Variables, v': Variables, outMsg: Message)
  {
    && outMsg.VoteReq?
    && outMsg.term == v.ms.term + 1
    && outMsg.candidate == c.idx
    && v' == v.(status := Candidate, ms := MonotonicTermState(v.ms.term + 1, {c.idx}, c.idx))
  }

  ghost predicate NextSendVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.send.Some?
    && msgOps.recv.Some?
    && ReceiveVoteReqSendVote(c, v, v', msgOps.recv.value, msgOps.send.value)
  }

  ghost predicate ReceiveVoteReqSendVote(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message)
  {
    && inMsg.VoteReq?
    && inMsg.term > v.ms.term
    && outMsg.Vote?
    && outMsg.candidate == inMsg.candidate
    && outMsg.voter == c.idx
    && outMsg.term == inMsg.term
    && v' == v.(status := Follower, ms := MonotonicTermState(inMsg.term, {}, inMsg.candidate))

  }

  ghost predicate NextRecvVoteStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveVote(c, v, v', msgOps.recv.value)
  }

  ghost predicate ReceiveVote(c: Constants, v: Variables, v': Variables, inMsg: Message)
  {
    && inMsg.Vote?
    && inMsg.candidate == c.idx
    && inMsg.term == v.ms.term
    && v.status.Candidate?
    && v' == v.(ms := v.ms.(acceptors := v.ms.acceptors + {inMsg.voter}))
  }

  ghost predicate NextBecomeLeaderStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.send.Some?
    && msgOps.recv.None?
    && SendDeclare(c, v, v', msgOps.send.value)
  }

  ghost predicate SendDeclare(c: Constants, v: Variables, v': Variables, outMsg: Message)
  {
    && outMsg.Declare?
    && outMsg.leader == c.idx
    && outMsg.term == v.ms.term
    && v.status.Candidate?
    && |v.ms.acceptors| >= c.f + 1
    && v' == v.(status := Leader)
  }

  ghost predicate NextLearnLeaderNewTermStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveDeclare1(c, v, v', msgOps.recv.value)
  }

  ghost predicate ReceiveDeclare1(c: Constants, v: Variables, v': Variables, inMsg: Message)
  {
    && inMsg.Declare?
    && inMsg.term > v.ms.term
    && v' == v.(status := Follower, ms := MonotonicTermState(inMsg.term, {}, inMsg.leader))
  }

  ghost predicate NextLearnLeaderSameTermStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.send.None?
    && msgOps.recv.Some?
    && ReceiveDeclare2(c, v, v', msgOps.recv.value)
  }

  ghost predicate ReceiveDeclare2(c: Constants, v: Variables, v': Variables, inMsg: Message)
  {
    && inMsg.Declare?
    && inMsg.term == v.ms.term
    && v' == v.(status := Follower)
  }


  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step {
      case InitCandidacyStep => NextInitCandidacyStep(c, v, v', msgOps)
      case SendVoteStep => NextSendVoteStep(c, v, v', msgOps)
      case RecvVoteStep => NextRecvVoteStep(c, v, v', msgOps)
      case BecomeLeaderStep => NextBecomeLeaderStep(c, v, v', msgOps)
      case LearnLeaderNewTermStep => NextLearnLeaderNewTermStep(c, v, v', msgOps)
      case LearnLeaderSameTermStep => NextLearnLeaderSameTermStep(c, v, v', msgOps)
    }
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }


}

