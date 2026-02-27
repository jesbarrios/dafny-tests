method AllPairsPositive(a: array<int>) returns (result: bool)
  ensures result <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] + a[j] > 0
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    // every ordered pair (p, q) whose row p < i has been checked
    invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> a[p] + a[q] > 0
  {
    var j := i + 1;
    while j < a.Length
      invariant i < j <= a.Length
      // outer invariant preserved across inner iterations
      invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> a[p] + a[q] > 0
      // current row i checked up to column j
      invariant forall q :: i < q < j ==> a[i] + a[q] > 0
    {
      if a[i] + a[j] <= 0 {
        result := false;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := true;
}
