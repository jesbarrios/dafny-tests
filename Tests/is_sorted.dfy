method IsSorted(a: array<int>) returns (sorted: bool)
  ensures sorted <==> forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
{
  var i := 0;
  while i + 1 < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i && j + 1 < a.Length ==> a[j] <= a[j+1]
  {
    if a[i] > a[i+1] {
      sorted := false;
      return;
    }
    i := i + 1;
  }
  sorted := true;
}
