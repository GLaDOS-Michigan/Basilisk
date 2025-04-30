include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

  // All responses received by clients are for valid requests
  ghost predicate Safety(c: Constants, v: Variables) 
    requires c.WF()
    requires v.WF(c)
  {
    v.Last().hosts[0].globalSum.Some? ==> v.Last().hosts[0].globalSum.value == Sum(SumOfSequences(c.hosts))
  }

  ghost function SumOfSequences(hosts: seq<Host.Constants>) : seq<int>
  {
      if |hosts| == 0 then [] else hosts[0].arr + SumOfSequences(hosts[1..])
  }


}
