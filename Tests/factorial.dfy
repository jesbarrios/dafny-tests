function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

method FactIter(n: nat) returns (f: nat)
  ensures f == Factorial(n)
{
  f := 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant f == Factorial(i)
  {
    i := i + 1;
    f := f * i;
  }
}
