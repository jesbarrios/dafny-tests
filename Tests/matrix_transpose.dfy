method Transpose(a: array2<int>) returns (b: array2<int>)
  ensures b.Length0 == a.Length1
  ensures b.Length1 == a.Length0
  ensures forall i, j :: 0 <= i < b.Length0 && 0 <= j < b.Length1 ==> b[i, j] == a[j, i]
{
  b := new int[a.Length1, a.Length0];
  var i := 0;
  while i < a.Length1
    invariant 0 <= i <= a.Length1
    // all rows of b before i are fully transposed
    invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length0 ==> b[r, c] == a[c, r]
  {
    var j := 0;
    while j < a.Length0
      invariant 0 <= j <= a.Length0
      // rows before i remain transposed across inner iterations
      invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length0 ==> b[r, c] == a[c, r]
      // current row i is transposed up to column j
      invariant forall c :: 0 <= c < j ==> b[i, c] == a[c, i]
    {
      b[i, j] := a[j, i];
      j := j + 1;
    }
    i := i + 1;
  }
}
