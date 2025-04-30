include "types.dfy"

/* The "client_server_ae protocol sourced from DuoAI (OSDI'22) 
 * Multiple clients can send requests to a server. The server processes each request 
 * and returns a response to the respective client. The server may process the 
 * requests out-of-order.*/

/***************************************************************************************
*                                      Server Host                                     *
***************************************************************************************/

module ServerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants

  datatype Variables = Variables(
    currentRequest: Option<Request>
  )
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There is exactly one server
    |grp_c| == 1
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c|
    && (forall idx:nat | idx < |grp_c| :: grp_v[idx].WF(grp_c[idx]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWF(grp_c, grp_v)
    && Init(grp_c[0], grp_v[0])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    v.currentRequest == None
  }

  datatype Step =
    ReceiveStep() | ProcessStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case ProcessStep => NextProcessStep(c, v, v', msgOps)
      case StutterStep => && v == v'
                          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && ReceiveRequest(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveRequest(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.currentRequest.None?
    && msg.RequestMsg?
    // update v'
    && v' == v.(currentRequest := Some(msg.r))
  }

  // Receive predicate trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  // ghost predicate ReceiveRequestTrigger(c: Constants, v: Variables, req: Request) {
  //   && v.currentRequest == Some(req)
  // }

  ghost predicate NextProcessStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendResponseMsg(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendResponseMsg(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.currentRequest.Some?
    // send message and update v'
    && v' == v.(currentRequest := None)
    && msg == ResponseMsg(v.currentRequest.value)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module ServerHost


/***************************************************************************************
*                                      Client Host                                     *
***************************************************************************************/

module ClientHost {
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary
  import opened Types

  datatype Constants = Constants(clientId: ClientId)

  ghost predicate ConstantsValidForGroup(c: Constants, clientId: ClientId) {
    c.clientId == clientId
  }

  datatype Variables = Variables(requests: MonotonicSet<nat>, responses: set<nat>)
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // The client's constants must match their group positions.
    forall clientId:ClientId | clientId < |grp_c|
      :: ConstantsValidForGroup(grp_c[clientId], clientId)
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c|
    && (forall idx:nat | idx < |grp_c| :: grp_v[idx].WF(grp_c[idx]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWF(grp_c, grp_v)
    && (forall clientId:ClientId | clientId < |grp_c| ::
        Init(grp_c[clientId], grp_v[clientId])
      )
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && 0 < |v.requests.s|  // non-deterministic set
    && v.responses == {}
  }

  datatype Step =
      RequestStep()
    | ReceiveStep() 
    | StutterStep

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps) {
    match step
      case RequestStep() => NextRequestStep(c, v, v', msgOps)
      case ReceiveStep => NextReceiveStep(c, v, v', msgOps)
      case StutterStep => 
          && v == v'
          && msgOps.send == msgOps.recv == None
  }

  ghost predicate NextRequestStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendRequestMsg(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendRequestMsg(c: Constants, v: Variables, v': Variables, msg: Message) {
    // send message and update v'
    && msg.RequestMsg?
    && msg.r.clientId == c.clientId
    && msg.r.reqId in v.requests.s
    && v' == v
  }

  ghost predicate NextReceiveStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && ReceiveResponse(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && msg.ResponseMsg?
    && msg.r.clientId == c.clientId
    // update v'
    && v' == v.(responses := v.responses + {msg.r.reqId})
  }

  // Receive response trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  // ghost predicate ReceiveResponseTrigger(c: Constants, v: Variables, reqId: nat) {
  //   && reqId in v.responses
  // }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module ClientHost
