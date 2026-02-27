function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}

// ── Case 1: invariant shifted by one step ─────────────────────────────────────
// f == Factorial(i+1) looks structurally like the correct f == Factorial(i).
// It happens to hold on entry (i=0 → Factorial(1)=1=f) but the loop body
// immediately breaks it: after i:=1, f:=1, we need Factorial(2)=2 but f=1.
method FactWrongStep(n: nat) returns (f: nat)
  ensures f == Factorial(n)
{
  f := 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant f == Factorial(i + 1)   // shifted: passes base case, fails at step
  {
    i := i + 1;
    f := f * i;
  }
}

// ── Case 2: invariant scaled by a constant ────────────────────────────────────
// f == Factorial(i) * 2 looks like a minor variation.  Fails immediately on
// entry: i=0, f=1, but Factorial(0)*2 = 2 ≠ 1.
method FactWrongScale(n: nat) returns (f: nat)
  ensures f == Factorial(n)
{
  f := 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant f == Factorial(i) * 2   // wrong constant factor; fails at init
  {
    i := i + 1;
    f := f * i;
  }
}

// ── Case 3: invariant too weak to imply the postcondition ─────────────────────
// f > 0 is genuinely true throughout (f starts at 1, only multiplied by
// positive values) so Dafny verifies the invariant — but it learns nothing
// useful about f at exit and cannot discharge the postcondition.
method FactTooWeak(n: nat) returns (f: nat)
  ensures f == Factorial(n)
{
  f := 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant f > 0               // maintained, but far too weak
  {
    i := i + 1;
    f := f * i;
  }
}
