method BinarySearch(a: array<int>, key: int) returns (idx: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures idx == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
  ensures idx != -1 ==> 0 <= idx < a.Length && a[idx] == key
{
  var lo, hi := 0, a.Length - 1;
  while lo <= hi
    invariant 0 <= lo <= a.Length
    invariant -1 <= hi < a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi < i < a.Length ==> key < a[i]
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] == key {
      return mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid - 1;
    }
  }
  return -1;
}
