include "../hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import Host

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }

    ghost predicate IsLeader(c: Constants, h: HostId) 
      requires WF(c)
      requires c.ValidHostId(h)
    {
      hosts[h].isLeader
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
  }

  datatype Step =
    | HostLocalStep(host: HostId)   // host can be nominated, or declare victory in this step
    | VoteReqStep(nominee: HostId, receiver: HostId, transmit: Transmit)
    | VoteStep(voter: HostId, nominee: HostId, transmit: Transmit)
    | StutterStep()

  
  ghost predicate NextHostLocalStep(c: Constants, v: Variables, v': Variables, host: HostId) 
    requires v.WF(c) && v'.WF(c)
  {
    // No transmission in this step
    && c.ValidHostId(host)
    && Host.Next(c.hosts[host], v.hosts[host], v'.hosts[host], MessageOps(None, None))
    && (forall idx: HostId | c.ValidHostId(idx) && idx != host
        :: v'.hosts[idx] == v.hosts[idx]
    )
  }

  ghost predicate NextVoteReqStep(c: Constants, v: Variables, v': Variables, nominee: HostId, receiver: HostId, transmit: Transmit)
    requires v.WF(c) && v'.WF(c)
  {
    // Sender action
    && nominee != receiver  // important to not introduce false
    && c.ValidHostId(nominee)
    && transmit.m.VoteReq?
    && Host.Next(c.hosts[nominee], v.hosts[nominee], v'.hosts[nominee], transmit.Send())
    // Receiver action
    && c.ValidHostId(receiver)
    && Host.Next(c.hosts[receiver], v.hosts[receiver], v'.hosts[receiver], transmit.Recv())
    // All others unchanged
    && (forall idx: HostId | c.ValidHostId(idx) && idx != nominee && idx != receiver
        :: v'.hosts[idx] == v.hosts[idx]
    )
  }

  ghost predicate NextVoteStep(c: Constants, v: Variables, v': Variables, voter: HostId, nominee: HostId, transmit: Transmit)
    requires v.WF(c) && v'.WF(c)
  {
    // Sender action
    && nominee != voter  // important to not introduce false
    && c.ValidHostId(voter)
    && transmit.m.Vote?
    && Host.Next(c.hosts[voter], v.hosts[voter], v'.hosts[voter], transmit.Send())
    // Receiver action
    && c.ValidHostId(nominee)
    && Host.Next(c.hosts[nominee], v.hosts[nominee], v'.hosts[nominee], transmit.Recv())
    // All others unchanged
    && (forall idx: HostId | c.ValidHostId(idx) && idx != nominee && idx != voter
        :: v'.hosts[idx] == v.hosts[idx]
    )
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
  {
    match step
      case HostLocalStep(host) => NextHostLocalStep(c, v, v', host)
      case VoteReqStep(nominee, receiver, transmit) => NextVoteReqStep(c, v, v', nominee, receiver, transmit)
      case VoteStep(voter, nominee, transmit) => NextVoteStep(c, v, v', voter, nominee, transmit)
      case StutterStep => v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    && v.WF(c)
    && v'.WF(c)
    && exists step :: NextStep(c, v, v', step)
  }

}