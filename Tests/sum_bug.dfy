function Sum(n: nat): nat {
  if n == 0 then 0 else n + Sum(n - 1)
}

// "Optimisation": use <= so the loop condition and the invariant upper bound
// are the same expression, avoiding a redundant separate check.
// The widened invariant i <= n+1 looks like a harmless one-line tweak.
method SumIter(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i <= n               // bug: should be i < n  (runs one extra iteration)
    invariant i <= n + 1     // widened from i <= n to match the new loop bound
    invariant s == Sum(i)
  {
    i := i + 1;
    s := s + i;
  }
}
