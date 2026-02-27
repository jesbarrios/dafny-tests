function Sum(n: nat): nat {
  if n == 0 then 0 else n + Sum(n - 1)
}

// ── Case 1: no invariants at all ──────────────────────────────────────────────
// Dafny treats every loop variable as completely unknown after the loop.
// Without any invariant, nothing is known about s or i at exit.
method SumNoInv(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i < n
  {
    i := i + 1;
    s := s + i;
  }
}

// ── Case 2: bounds invariant only ────────────────────────────────────────────
// i <= n tells Dafny the cursor is in range, but says nothing about
// the relationship between s and the partial sum.  Postcondition still fails.
method SumBoundsOnly(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant i <= n    // correct but insufficient
  {
    i := i + 1;
    s := s + i;
  }
}

// ── Case 3: wrong functional invariant ───────────────────────────────────────
// s == Sum(i) + 1 looks structurally similar to the correct invariant.
// It fails immediately at initialisation (s=0, i=0 → 0 == Sum(0)+1 = 1 is false)
// and is also inconsistent with the postcondition at exit.
method SumWrongInv(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant i <= n
    invariant s == Sum(i) + 1   // off-by-one in the invariant itself
  {
    i := i + 1;
    s := s + i;
  }
}
