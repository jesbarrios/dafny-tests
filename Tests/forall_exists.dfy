// forall_exists.dfy
//
// DUAL QUANTIFICATION
//   result <==> forall i :: 0<=i<a.Length ==> exists j :: 0<=j<b.Length && a[i]==b[j]
//
// Proof strategy
// --------------
// TRUE  branch  (every element of a has a match in b):
//   ghost map<int,int> witnesses  maps each verified index k in a to a witness j in b
//   Outer-loop invariant: witnesses[k] is valid for all k < i
//   After the loop, a ghost `forall` statement peels the witness out for each k,
//   proving the existential without asking Z3 to search.
//
// FALSE branch  (some element of a has no match in b):
//   Inner-loop invariant: !found ==> forall k < j :: a[i] != b[k]  ("exclusion zone")
//   On normal exit with !found: j == b.Length, so the full b was scanned.
//   Explicit assert !(exists jj :: ...) names index i as a counterexample,
//   letting Z3 discharge !(forall ...) without searching.
//
// Avoiding timeouts
// -----------------
// Dual quantification is notoriously hard for SMT solvers.  We sidestep the
// difficulty by never asking Z3 to *find* witnesses — we record them in a ghost
// map and hand them back explicitly.  The only quantifier Z3 has to deal with
// in each invariant is a single-level forall over one loop variable.

method {:timeLimit 20} HasWitness(a: array<int>, b: array<int>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < a.Length ==> exists j :: 0 <= j < b.Length && a[i] == b[j]
{
  // witnesses[k] = the index j in b with a[k] == b[j], for each k we have verified
  ghost var witnesses: map<int, int> := map[];

  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    // Core invariant: witnesses covers [0..i) with valid, matching indices
    invariant forall k :: 0 <= k < i ==>
                k in witnesses &&
                0 <= witnesses[k] < b.Length &&
                a[k] == b[witnesses[k]]
  {
    // --- Inner search: scan b for a[i] ---
    var j     := 0;
    ghost var wj: int := 0;  // witness index; only meaningful when found == true
    var found := false;

    // Use the loop condition to carry "!found", so on normal exit we get
    // j >= b.Length (negation of j < b.Length) for free — no break needed.
    while j < b.Length && !found
      decreases b.Length - j + (if !found then 1 else 0)
      invariant 0 <= j <= b.Length
      // Exclusion zone: b[0..j) contains no element equal to a[i]
      invariant !found ==> forall k :: 0 <= k < j ==> a[i] != b[k]
      // Witness is valid whenever we have flagged a hit
      invariant  found ==> 0 <= wj < b.Length && a[i] == b[wj]
    {
      if b[j] == a[i] {
        wj    := j;
        found := true;
        // Loop condition becomes false (because !found is now false); exits next check
      } else {
        j := j + 1;
        // Invariant maintained: b[old j] != a[i], so exclusion zone grows by one
      }
    }
    // After the inner loop:
    //   invariants still hold
    //   if !found: loop exited because j >= b.Length (i.e. j == b.Length exactly)
    //   if  found: wj is a valid witness

    if !found {
      // j == b.Length: all of b was scanned with no match
      assert forall k :: 0 <= k < b.Length ==> a[i] != b[k];
      // Restate as a negated existential — the form the postcondition needs
      assert !(exists jj :: 0 <= jj < b.Length && a[i] == b[jj]);
      // i ∈ [0, a.Length) is a concrete counterexample, so the outer forall is false
      assert !(forall ii :: 0 <= ii < a.Length ==> exists jj :: 0 <= jj < b.Length && a[ii] == b[jj]);
      result := false;
      return;
    }

    // found == true: record the witness and move to the next element of a
    witnesses := witnesses[i := wj];
    i := i + 1;
  }

  // All indices in a have witnesses.  Use a ghost forall-statement to prove
  // the existential for each k by pointing at the concrete witness witnesses[k].
  // This avoids asking Z3 to search; we merely ask it to *check* each witness.
  forall k | 0 <= k < a.Length
    ensures exists j :: 0 <= j < b.Length && a[k] == b[j]
  {
    // witnesses[k] is the j that satisfies the existential
    assert k in witnesses &&
           0 <= witnesses[k] < b.Length &&
           a[k] == b[witnesses[k]];
  }

  assert forall i :: 0 <= i < a.Length ==> exists j :: 0 <= j < b.Length && a[i] == b[j];
  result := true;
}
