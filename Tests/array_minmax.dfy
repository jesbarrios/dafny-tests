method FindMinMax(a: array<int>) returns (min: int, max: int)
  requires a.Length > 0
  ensures min in a[..]
  ensures max in a[..]
  ensures forall i :: 0 <= i < a.Length ==> min <= a[i] <= max
{
  min := a[0];
  max := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant min in a[..i]
    invariant max in a[..i]
    invariant forall j :: 0 <= j < i ==> min <= a[j] <= max
  {
    if a[i] < min { min := a[i]; }
    if a[i] > max { max := a[i]; }
    i := i + 1;
  }
}
