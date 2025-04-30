include "UtilitiesLibrary.dfy"

module MonotonicityLibrary {
  import opened UtilitiesLibrary

  datatype MonotonicWriteOnceOption<T> = WOSome(value:T) | WONone
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicWriteOnceOption<T>) {
      past.WOSome? ==> past == this
    }
  }

  datatype MonotonicNatOption = MNSome(value: nat) | MNNone
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicNatOption) {
      past.MNSome? ==> (this.MNSome? && past.value <= this.value)
    }
  }

  datatype MonotonicSet<T> = MonotonicSet(s: set<T>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicSet<T>) 
    {
      && past.s <= this.s
    }

    ghost function Value() : set<T> {
      s
    }

    ghost function Add(e: T) : MonotonicSet<T> {
      MonotonicSet(s + {e})
    }

    ghost function Contains(e: T) : bool {
      e in s
    }
    
    ghost function IsSubsetOf(other: set<T>) : bool {
      s <= other
    }

    ghost function IsSubsetOfMonotonic(other: MonotonicSet<T>) : bool {
      s <= other.s
    }
  }

  lemma MonotonicSetContainmentLemma<T>(ms: MonotonicSet<T>, s: set<T> ) 
    requires forall x | ms.Contains(x) :: x in s
    ensures ms.IsSubsetOf(s)
  {}
 
  datatype MonotonicSeq<T> = MonotonicSeq(s: seq<T>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicSeq<T>) {
      && |past.s| <= |s| 
      && (forall i | 0 <= i < |past.s| :: past.s[i] == s[i])
    }
  }

  datatype MonotonicMap<K, V> = MonotonicMap(m: map<K, V>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicMap<K, V>) {
      forall k | k in past.m :: (
        && k in m
        && past.m[k] == m[k]
      )
    }
  }

  datatype MonotonicBool = MonotonicBool(b: bool)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicBool) {
      past.b ==> b
    }

    ghost function Value() : bool {
      b
    }
  }
}
