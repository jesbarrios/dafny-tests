method FindMaxIdx(a: array<int>) returns (max: int, idx: int)
  requires a.Length > 0
  ensures 0 <= idx < a.Length
  ensures max == a[idx]
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
{
  max := a[0];
  idx := 0;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= idx < i
    invariant max == a[idx]
    invariant forall j :: 0 <= j < i ==> a[j] <= max
  {
    if a[i] > max {
      max := a[i];
      idx := i;
    }
    i := i + 1;
  }
}
