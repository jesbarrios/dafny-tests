function Product(n: nat): nat {
  if n == 0 then 1 else n * Product(n - 1)
}

method ProductIter(n: nat) returns (p: nat)
  ensures p == Product(n)
{
  p := 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant p == Product(i)
  {
    i := i + 1;
    p := p * i;
  }
}
