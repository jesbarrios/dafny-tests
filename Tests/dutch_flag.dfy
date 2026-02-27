// Dutch National Flag algorithm: partition array into three zones.
//
// Three-pointer algorithm:
//   lo  – next slot in the < pivot zone
//   mid – next unclassified element
//   hi  – last unclassified element
//
// Picture at each step:
//   | < pivot | == pivot | unclassified | > pivot |
//   0        lo         mid           hi+1      a.Length
//
// Three cases:
//   a[mid] < pivot  → swap a[lo]↔a[mid], lo++, mid++
//   a[mid] == pivot → mid++
//   a[mid] > pivot  → swap a[mid]↔a[hi], hi--
//
// Exit (mid > hi): unclassified zone is empty.
// Combined with mid <= hi+1 (invariant): mid == hi+1, giving exact zone boundaries.

method DutchFlag(a: array<int>, pivot: int) returns (lo: int, mid: int)
  modifies a
  ensures 0 <= lo <= mid <= a.Length
  ensures forall i :: 0 <= i < lo         ==> a[i] < pivot
  ensures forall i :: lo <= i < mid       ==> a[i] == pivot
  ensures forall i :: mid <= i < a.Length ==> a[i] > pivot
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  lo  := 0;
  mid := 0;
  var hi: int := a.Length - 1;

  while mid <= hi
    invariant 0 <= lo <= mid          // lo and mid sweep rightward
    invariant mid <= hi + 1           // unclassified zone [mid, hi] may be empty
    invariant -1 <= hi < a.Length     // hi sweeps leftward; -1 when fully processed
    invariant forall k :: 0 <= k < lo         ==> a[k] < pivot
    invariant forall k :: lo <= k < mid       ==> a[k] == pivot
    invariant forall k :: hi < k < a.Length   ==> a[k] > pivot
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases hi - mid + 1
  {
    if a[mid] < pivot {
      // Move a[mid] into the < zone; the old a[lo] (== pivot) slides right.
      a[lo], a[mid] := a[mid], a[lo];
      lo  := lo  + 1;
      mid := mid + 1;
    } else if a[mid] == pivot {
      // Already in the right zone; just extend it.
      mid := mid + 1;
    } else {
      // Move a[mid] into the > zone; a[hi] (unclassified) comes back for re-check.
      a[mid], a[hi] := a[hi], a[mid];
      hi := hi - 1;
    }
  }
  // At exit: mid > hi  and  mid <= hi+1  =>  mid == hi+1.
  // Invariants instantiate directly as the three postcondition foralls.
}
