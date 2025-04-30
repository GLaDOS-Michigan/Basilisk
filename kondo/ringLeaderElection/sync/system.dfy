include "../hosts.dfy"

module System {
import opened UtilitiesLibrary
import opened Types
import Host

datatype Constants = Constants(
  hosts: seq<Host.Constants>)
{
  ghost predicate ValidIdx(id: int) {
    0 <= id < |hosts|
  }

  ghost predicate UniqueIds() {
    forall i, j | ValidIdx(i) && ValidIdx(j) && hosts[i].hostId == hosts[j].hostId :: i == j
  }

  ghost predicate WF() {
    && 0 < |hosts|
    && UniqueIds()
  }
}

datatype Variables = Variables(
  hosts: seq<Host.Variables>)
{
  ghost predicate WF(c: Constants) {
    && c.WF()
    && Host.GroupWF(c.hosts, hosts)
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && Host.GroupInit(c.hosts, v.hosts)
}

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, actor: nat, transmit: Transmit)
  requires v.WF(c) && v'.WF(c)
{
  // Sender action
  && c.ValidIdx(actor)
  && Host.Next(c.hosts[actor], v.hosts[actor], v'.hosts[actor], transmit.Send())
  // Receiver action
  && var succ := Successor(|c.hosts|, actor);
  && Host.Next(c.hosts[succ], v.hosts[succ], v'.hosts[succ], transmit.Recv())     // step receiver
  // All others unchanged
  && forall idx:nat | 
      && c.ValidIdx(idx) 
      && idx != actor
      && idx != succ
      :: 
      v'.hosts[idx] == v.hosts[idx]
}

datatype Step = TransmissionStep(actor: nat, transmit: Transmit)

ghost predicate NextStep(c:Constants, v: Variables, v': Variables, step: Step) 
  requires v.WF(c) && v'.WF(c)
{
  match step {
      case TransmissionStep(actor, transmit) => Transmission(c, v, v', actor, transmit)
  }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && exists step :: NextStep(c, v, v', step)
}

}  // end module DistributedSystem
