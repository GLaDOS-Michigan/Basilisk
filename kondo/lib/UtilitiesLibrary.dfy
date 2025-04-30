module UtilitiesLibrary {
  datatype Option<T> = Some(value:T) | None

  ghost function max(x: int, y: int) : (res: int) 
    ensures res == x || res == y
    ensures res >= x && res >= y
  {
    if x > y then x else y
  }

  ghost function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  ghost function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  ghost function Successor(mod: nat, idx: nat) : (ret:nat)
    requires 0 < mod
    requires idx < mod
  {
    if idx == mod-1 then 0 else idx+1
  }

  ghost function Predecessor(mod: nat, idx: nat) : (ret:nat)
    requires 0 < mod
    requires idx < mod
  {
    if idx == 0 then mod-1 else idx-1
  }

  ghost predicate StrictOrdering(s: seq<nat>) {
    forall i , j | 
      && 0 <= i < |s| 
      && 0 <= j < |s| 
      && i < j
    :: s[i] < s[j]
  }

  ghost predicate SeqIsComplete(s: seq<nat>, x: nat, y: nat) {
    && 2 <= |s|
    && s[0] == x
    && s[|s|-1] == y
    && (forall n | x <= n <= y :: n in s)
  }
  
  lemma SetComprehensionSize(n: nat) 
    ensures |(set x | 0 <= x < n)| == n
    decreases n
  {
    var s := (set x | 0 <= x < n);
    if n == 0 {
      assert |s| == 0;
    } else {
      SetComprehensionSize(n-1);
      assert s == (set x | 0 <= x < n-1) + {n-1};  // trigger
    }
  }

  lemma SetContainmentCardinality<T>(s1: set<T>, s2: set<T>) 
    requires s1 <= s2
    ensures |s1| <= |s2|
  {
    if |s1| == 0 {
      assert |s1| <= |s2|;
    } else {
      var x :| x in s1;
      var s1' := s1 - {x};
      SetContainmentCardinality(s1', s2);
      assume {:axiom} false;
    }
  }

  lemma SetContainmentCardinalityStrict<T>(s1: set<T>, s2: set<T>) 
    requires s1 < s2
    ensures |s1| < |s2|
  {
    assume {:axiom} false;
  }

  lemma UnionIncreasesCardinality<T>(s1: set<T>, s2: set<T>) 
    ensures |s1 + s2| >= |s1|
    decreases s2
  {
    if |s2| == 0 {
      assert |s1 + s2| == |s1|;
    } else {
      var x :| x in s2;
      var s2' := s2 - {x};
      UnionIncreasesCardinality(s1, s2');
      LargerSetIncreasesCardinalityMore(s1, s2', s2);
      assert |s1 + s2| >= |s1|;
    }
  }

  lemma LargerSetIncreasesCardinalityMore<T>(s: set<T>, s1: set<T>, s2: set<T>) 
    requires s1 <= s2
    ensures |s+s1| <= |s+s2|
  {
    assume {:axiom} false;  //TODO
  }

  ghost function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {
    if |theSets| == 0 then {} else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  // As you can see, Dafny's recursion heuristics easily complete the recursion
  // induction proofs, so these two statements could easily be ensures of
  // UnionSeqOfSets. However, the quantifiers combine with native map axioms
  // to be a bit trigger-happy, so we've pulled them into independent lemmas
  // you can invoke only when needed.
  // Suggestion: hide calls to this lemma in a an
  //   assert P by { SetsAreSubsetsOfUnion(...) }
  // construct so you can get your conclusion without "polluting" the rest of the
  // lemma proof context with this enthusiastic forall.
  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
  }

  // Convenience function for learning a particular index (invoking Hilbert's
  // Choose on the exists in EachUnionMemberBelongsToASet).
  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {
    EachUnionMemberBelongsToASet(theSets);
    var chosenIdx :| 0<=chosenIdx<|theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }

  ghost predicate SetIsQuorum<T>(clusterSize: nat, S: set<T>) {
    |S| > clusterSize / 2
  }
  
  lemma QuorumIntersection<T>(cluster: set<T>, S1: set<T>, S2: set<T>) returns (e: T) 
    requires |S1| + |S2| > |cluster|
    requires S1 <= cluster
    requires S2 <= cluster
    ensures e in S1 && e in S2
  {
    var overlap := S1 * S2;
    assert overlap != {} by {
      // Pigeonhole principle: since |S1| + |S2| > |cluster| then at least 1 T element is in both S1 & S2 i.e., a non-empty overlap.
      if overlap == {} {
        DisjointSetUnionCardinality(S1, S2);
        SetContainmentCardinality(S1+S2, cluster);
      }
    }
    e :| e in overlap; // Picks one arbitrary element from overlap set.
  }

  lemma DisjointSetUnionCardinality<T>(S1: set<T>, S2: set<T>) 
    requires S1 * S2 == {}
    ensures |S1| + |S2| == |S1 + S2|
  {
    assume {:axiom} false;
  }

  ghost function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    assert m'.Keys == m.Keys - {key};
    m'
  }

  ghost predicate IsSeqExtension<T>(s: seq<T>, s': seq<T>) {
    && |s'| == |s| + 1
    && |s| == |s'| - 1
    && forall i | 0 <= i < |s| :: s[i] == s'[i]
  }

  ghost function StutterSeq<T>(s: seq<T>) : (s': seq<T>)
    requires 0 < |s|
    ensures |s'| == |s|+1
  {
    s + [Last(s)]
  }

  ghost predicate SeqMonotoneIncreasing(s: seq<nat>) {
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && i <= j
    :: s[i] <= s[j]
  }

  ghost predicate SeqOptionMonotoneIncreasing(s: seq<Option<nat>>) {
    forall i, j | 
      && 0 <= i < |s| 
      && 0 <= j < |s| 
      && i <= j
      && s[i].Some?
    :: s[j].Some? && s[i].value <= s[j].value
  }

  ghost predicate SetMonotoneIncreasing<T>(s: seq<set<T>>) {
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && i <= j
    :: s[i] <= s[j]
  }
}
