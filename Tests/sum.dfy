function Sum(n: nat): nat {
  if n == 0 then 0 else n + Sum(n - 1)
}

method SumIter(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant i <= n
    invariant s == Sum(i)
  {
    i := i + 1;
    s := s + i;
  }
}
