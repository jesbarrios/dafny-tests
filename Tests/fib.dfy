function Fib(n: nat): nat {
  if n == 0 then 0
  else if n == 1 then 1
  else Fib(n - 1) + Fib(n - 2)
}

method FibIter(n: nat) returns (f: nat)
  ensures f == Fib(n)
{
  var a, b := 0, 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant a == Fib(i)
    invariant b == Fib(i + 1)
  {
    a, b := b, a + b;
    i := i + 1;
  }
  f := a;
}
