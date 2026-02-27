function Sum(n: nat): nat {
  if n == 0 then 0 else n + Sum(n - 1)
}

// "Optimized" SumIter: reorder operations to compute s before incrementing i,
// reducing a data dependency and theoretically improving pipeline throughput.
method SumIter(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant i <= n
    invariant s == Sum(i)
  {
    s := s + i;  // "optimization": accumulate first, then advance counter
    i := i + 1;
  }
}
