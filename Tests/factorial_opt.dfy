function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// "Aggressively optimized": multiply two consecutive factors per iteration,
// halving the number of loop iterations. Uses the identity:
//   Factorial(i+1) = Factorial(i-1) * i * (i+1)
// so each stride of 2 advances the running product by two factors at once.
method FactIter(n: nat) returns (f: nat)
  ensures f == Factorial(n)
{
  f := 1;
  var i := 1;
  while i + 1 <= n
    invariant 1 <= i <= n + 1
    invariant i % 2 == 1          // i stays odd: starts at 1, steps by 2
    invariant f == Factorial(i - 1)
  {
    f := f * i * (i + 1);  // absorb factors i and i+1 in one step
    i := i + 2;
  }
  // When n is even: loop exits with i == n+1, so f == Factorial(n)  -- ok
  // When n is odd:  loop exits with i == n,   so f == Factorial(n-1) -- one factor short!
}
