// Spec: partial dot product of row i of a with column j of b, summing k terms.
// DotProduct(a, b, i, j, n) = sum_{k=0}^{n-1} a[i,k] * b[k,j]
function DotProduct(a: array2<int>, b: array2<int>, i: int, j: int, n: int): int
  requires a.Length1 == b.Length0
  requires 0 <= i < a.Length0
  requires 0 <= j < b.Length1
  requires 0 <= n <= a.Length1
  reads a, b
{
  if n == 0 then 0
  else DotProduct(a, b, i, j, n - 1) + a[i, n - 1] * b[n - 1, j]
}

method MatMult(a: array2<int>, b: array2<int>) returns (c: array2<int>)
  requires a.Length1 == b.Length0
  ensures c.Length0 == a.Length0
  ensures c.Length1 == b.Length1
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < b.Length1 ==>
    c[i, j] == DotProduct(a, b, i, j, a.Length1)
{
  c := new int[a.Length0, b.Length1];
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    // all rows before i are fully computed
    invariant forall r, s :: 0 <= r < i && 0 <= s < b.Length1 ==>
      c[r, s] == DotProduct(a, b, r, s, a.Length1)
  {
    var j := 0;
    while j < b.Length1
      invariant 0 <= j <= b.Length1
      // rows before i remain correct across inner iterations
      invariant forall r, s :: 0 <= r < i && 0 <= s < b.Length1 ==>
        c[r, s] == DotProduct(a, b, r, s, a.Length1)
      // current row i is correct up to column j
      invariant forall s :: 0 <= s < j ==>
        c[i, s] == DotProduct(a, b, i, s, a.Length1)
    {
      // accumulate dot product for cell (i, j) in a local variable;
      // c[i, j] is only written once, keeping earlier invariants intact
      var acc := 0;
      var k := 0;
      while k < a.Length1
        invariant 0 <= k <= a.Length1
        invariant acc == DotProduct(a, b, i, j, k)
      {
        acc := acc + a[i, k] * b[k, j];
        k := k + 1;
      }
      c[i, j] := acc;
      j := j + 1;
    }
    i := i + 1;
  }
}
