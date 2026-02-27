// Swap elements at positions i and j in array a.
// Postconditions:
//   1. Position i holds the old value at j, and vice versa.
//   2. Every other position is unchanged.
//   3. The multiset of elements is preserved (same elements, different arrangement).

method Swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  a[i], a[j] := a[j], a[i];
}
