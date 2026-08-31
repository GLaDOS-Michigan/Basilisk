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

  datatype MonotonicMapOfWriteOnceOptions<K, V> = MonotonicMapOfWriteOnceOptions(m: map<K, MonotonicWriteOnceOption<V>>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicMapOfWriteOnceOptions<K, V>) {
      forall k | k in past.m :: (
        && k in m
        && m[k].SatisfiesMonotonic(past.m[k])
      )
    }
    ghost function AddKey(k: K) : MonotonicMapOfWriteOnceOptions<K, V> {
      if k in m then
        this
      else
        MonotonicMapOfWriteOnceOptions(m[k := WONone])
    }
    ghost function Add(k: K, v: V) : MonotonicMapOfWriteOnceOptions<K, V> {
      MonotonicMapOfWriteOnceOptions(m[k := WOSome(v)])
    }
  }

  datatype MonotonicMapOfSets<K, V> = MonotonicMapOfSets(m: map<K, MonotonicSet<V>>)
  {
    ghost predicate SatisfiesMonotonic(past: MonotonicMapOfSets<K, V>) {
      forall k | k in past.m :: (
        && k in m
        && m[k].SatisfiesMonotonic(past.m[k])
      )
    }
    ghost function AddKey(k: K) : MonotonicMapOfSets<K, V> {
      if k in m then
        this
      else
        MonotonicMapOfSets(m[k := MonotonicSet({})])
    }
    ghost function Add(k: K, v: V) : MonotonicMapOfSets<K, V> {
      if k in m then
        MonotonicMapOfSets(m[k := m[k].Add(v)])
      else
        MonotonicMapOfSets(m[k := MonotonicSet({v})])
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
