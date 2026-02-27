// unique_check.dfy
// HasDuplicates returns true iff the array contains at least one duplicate value.
//
// Ghost map<int,int> maps each value to its first occurrence index, giving a
// concrete witness for the existential in the postcondition.
// A `break` on first find keeps the seen-map simple (no post-duplicate updates).

method HasDuplicates(a: array<int>) returns (hasDup: bool)
  ensures hasDup <==> exists i, j :: 0 <= i < j < a.Length && a[i] == a[j]
{
  ghost var seen: map<int, int> := map[];
  hasDup := false;
  var i := 0;

  while i < a.Length
    // Bounds
    invariant 0 <= i <= a.Length
    // Map integrity: seen[v] is the index of v's first occurrence in a[0..i)
    invariant forall v :: v in seen ==> 0 <= seen[v] < i && a[seen[v]] == v
    // Coverage: every element processed so far appears in seen
    invariant forall k :: 0 <= k < i ==> a[k] in seen
    // No dup yet  ==>  a[0..i) has all-distinct elements
    invariant !hasDup ==> forall p, q :: 0 <= p < q < i ==> a[p] != a[q]
    // Dup found   ==>  a concrete witness pair exists in the full array
    invariant hasDup ==> exists p, q :: 0 <= p < q < a.Length && a[p] == a[q]
  {
    if a[i] in seen {
      // seen[a[i]] is a strictly earlier index whose element equals a[i].
      // Lay out the witness explicitly so Dafny can close the existential.
      ghost var witness := seen[a[i]];
      assert 0 <= witness < i < a.Length; // in-range and strictly before i
      assert a[witness] == a[i];          // same value  (map integrity)
      assert exists p, q :: 0 <= p < q < a.Length && a[p] == a[q];
      hasDup := true;
      break;
    }
    // a[i] is fresh — record its index and advance
    seen := seen[a[i] := i];
    i := i + 1;
  }
  // Normal exit (i == a.Length, hasDup == false):
  //   !hasDup ==> forall p,q :: 0<=p<q<a.Length ==> a[p]!=a[q]
  //   which is exactly the negation of the existential  =>  postcondition holds.
}
