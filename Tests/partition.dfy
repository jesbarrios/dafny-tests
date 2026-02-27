method Partition(a: array<int>, pivot: int) returns (idx: int)
  modifies a
  ensures 0 <= idx <= a.Length
  ensures forall i :: 0 <= i < idx ==> a[i] <= pivot
  ensures forall i :: idx <= i < a.Length ==> a[i] > pivot
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var lo := 0;
  var i  := 0;
  while i < a.Length
    invariant 0 <= lo <= i <= a.Length
    invariant forall k :: 0 <= k < lo      ==> a[k] <= pivot  // left zone
    invariant forall k :: lo <= k < i      ==> a[k] >  pivot  // right zone
    invariant multiset(a[..]) == multiset(old(a[..]))          // permutation
  {
    if a[i] <= pivot {
      a[lo], a[i] := a[i], a[lo];
      lo := lo + 1;
    }
    i := i + 1;
  }
  idx := lo;
}
