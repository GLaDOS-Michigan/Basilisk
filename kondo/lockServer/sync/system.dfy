include "../hosts.dfy"

module System {
  import opened UtilitiesLibrary
  import opened Types
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
} // end datatype Constants

datatype Variables = Variables(
  clients: seq<ClientHost.Variables>,
  server: seq<ServerHost.Variables>
) {
  ghost predicate WF(c: Constants) {
    && c.WF()
    && ClientHost.GroupWF(c.clients, clients)
    && var allClients := (set x | 0 <= x < |c.clients| :: c.clients[x].myId);
    && ServerHost.GroupWF(c.server, server, allClients)
  }
} // end datatype Variables


//// System Transitions ////

ghost predicate Init(c: Constants, v: Variables) {
  && v.WF(c)
  && var allClients := (set x | 0 <= x < |c.clients| :: c.clients[x].myId);
  && ClientHost.GroupInit(c.clients, v.clients)
    && ServerHost.GroupInit(c.server, v.server, allClients)
}

datatype Step = 
  | Grant(client: HostId, transmit: Transmit)
  | Release(client: HostId, transmit: Transmit)
  | StutterStep()

// Server gives lock to client
ghost predicate NextGrantStep(c: Constants, v: Variables, v': Variables, client: HostId, transmit: Transmit) 
  requires v.WF(c) && v'.WF(c)
{
  // Server action
  && transmit.m.Grant?
  && ServerHost.Next(c.server[0], v.server[0], v'.server[0], transmit.Send())
  // Client action
  && c.ValidClientIdx(client)
  && ClientHost.Next(c.clients[client], v.clients[client], v'.clients[client], transmit.Recv())
  // All others unchanged
  && (forall x | c.ValidClientIdx(x) && x != client
      :: v'.clients[x] == v.clients[x])
}

// Client releases lock back to server
ghost predicate NextReleaseStep(c: Constants, v: Variables, v': Variables, client: HostId, transmit: Transmit) 
  requires v.WF(c) && v'.WF(c)
{
  // Client action
  && transmit.m.Release?
  && c.ValidClientIdx(client)
  && ClientHost.Next(c.clients[client], v.clients[client], v'.clients[client], transmit.Send())
  // Server action
  && ServerHost.Next(c.server[0], v.server[0], v'.server[0], transmit.Recv())
  // All others unchanged
  && (forall x | c.ValidClientIdx(x) && x != client
      :: v'.clients[x] == v.clients[x])
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  requires v.WF(c) && v'.WF(c)
{
  match step
    case Grant(client, transmit) => NextGrantStep(c, v, v', client, transmit)
    case Release(client, transmit) => NextReleaseStep(c, v, v', client, transmit)
    case StutterStep => v' == v
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  && v.WF(c)
  && v'.WF(c)
  && exists step :: NextStep(c, v, v', step)
}
} // end module System