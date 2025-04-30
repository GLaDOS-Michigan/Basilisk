include "../hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
  import Host

datatype Constants = Constants(
  hosts: seq<Host.Constants>
)
{
  ghost predicate WF() {
    && 0 < |hosts|
    && UniqueIds()
  }
  
  ghost predicate UniqueIds() {
      forall i, j | ValidIdx(i) && ValidIdx(j) && hosts[i].hostId == hosts[j].hostId :: i == j
    }

  ghost predicate ValidIdx(id: int) {
    0 <= id < |hosts|
  }
} // end datatype Constants

datatype Variables = Variables(
  hosts: seq<Host.Variables>
) {
  ghost predicate WF(c: Constants) {
    && c.WF()
      && Host.GroupWF(c.hosts, hosts)
  }
} // end datatype Variables


//// System Transitions ////

ghost predicate Init(c: Constants, v: Variables) {
  && v.WF(c)
  && Host.GroupInit(c.hosts, v.hosts)
}

datatype Step = 
  | Transfer(sender: HostId, receiver: HostId, transmit: Transmit)
  | StutterStep()


// Leader sends Prepare message to Acceptor. Acceptor buffers it in its pendingPrepare field 
ghost predicate NextTransferStep(c: Constants, v: Variables, v': Variables, sender: HostId, receiver: HostId, transmit: Transmit) 
  requires v.WF(c) && v'.WF(c)
{
  // Sender action
  && c.ValidIdx(sender)
  && transmit.m.Grant?
  && Host.Next(c.hosts[sender], v.hosts[sender], v'.hosts[sender], transmit.Send())
  // Receiver action
  && sender != receiver
  && c.ValidIdx(receiver)
  && Host.Next(c.hosts[receiver], v.hosts[receiver], v'.hosts[receiver], transmit.Recv())
  // All others unchanged
  && (forall otherHostIdx | 
        && c.ValidIdx(otherHostIdx) 
        && otherHostIdx != sender
        && otherHostIdx != receiver :: v'.hosts[otherHostIdx] == v.hosts[otherHostIdx])
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
    case Transfer(sender, receiver, transmit) => NextTransferStep(c, v, v', sender, receiver, transmit)
    case StutterStep => v' == v
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && exists step :: NextStep(c, v, v', step)
}
} // end module System