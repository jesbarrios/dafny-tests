// ghost_seq_quantifier.dfy
//
// FORALL-EXISTS OVER SEQUENCE INDICES  (strict inequality chain)
//   valid <==> forall i :: 0 <= i < |trace|-1 ==>
//                exists k :: i < k < |trace| && trace[i] < trace[k]
//
// Plain English: every element except the last has some later element
// that is strictly greater than it.
//
// Proof strategy — no explicit witness map
// ----------------------------------------
// Contrast with forall_exists.dfy, which uses ghost map<int,int> to
// record one witness per verified position and then discharges the
// postcondition with a ghost forall-statement.
//
// Here, the existential is carried *directly* in the inner loop's
// invariant.  A boolean `found` flag is enough:
//
//   found  ==>  exists k :: i < k < |trace| && trace[i] < trace[k]
//
// At the break point the invariant is proved with the concrete index j,
// but after the loop only the existential survives — no map, no stored
// index.
//
// Outer-loop invariant — disjunction form
// ----------------------------------------
// To avoid a monotonicity gap between "forall p < i" and the spec bound
// "|trace|-1", we write the invariant over the full spec range using a
// disjunction:
//
//   forall p :: 0 <= p < |trace|-1 ==>
//     p >= i  ||  exists k :: p < k < |trace| && trace[p] < trace[k]
//
//   "Position p is either not yet visited (p >= i) or already has a witness."
//
// Initialization (i=0):  p >= 0 is always true — trivially satisfied.
// Maintenance:           on i := i+1, we have a fresh witness for p == i_old,
//                        so the disjunct flips from the left side to the right.
// Loop exit (i >= |trace|-1):  for all p < |trace|-1 we have p < |trace|-1 <= i,
//                        so "p >= i" is false and the right disjunct must hold.
//                        This *directly* yields the postcondition; no extra assert.
//
// FALSE path: inner loop exits normally (j == |trace|) with !found.
//             The "exclusion zone" invariant covers the whole suffix.
//             We assert !(exists k :: ...), giving Z3 position i as a
//             concrete counterexample for !(forall ...).

method ValidGhostTrace(trace: seq<int>) returns (valid: bool)
  ensures valid <==> forall i :: 0 <= i < |trace|-1 ==>
                       exists k :: i < k < |trace| && trace[i] < trace[k]
{
  var i := 0;
  while i < |trace| - 1
    invariant 0 <= i
    // Disjunction over the full spec range avoids a monotonicity gap at exit
    invariant forall p :: 0 <= p < |trace| - 1 ==>
                p >= i || exists k :: p < k < |trace| && trace[p] < trace[k]
    decreases |trace| - i
  {
    // ── Inner search: scan trace[i+1..] for any element strictly > trace[i] ──
    var j := i + 1;
    var found := false;

    while j < |trace|
      invariant i < j <= |trace|
      // Exclusion zone: every suffix element seen so far is <= trace[i]
      invariant !found ==> forall q :: i < q < j ==> trace[q] <= trace[i]
      // Witness existence proved at break with k=j; only existential survives
      invariant  found ==> exists k :: i < k < |trace| && trace[i] < trace[k]
      decreases |trace| - j
    {
      if trace[j] > trace[i] {
        found := true;   // j witnesses the existential; stored implicitly
        break;
      }
      j := j + 1;
    }
    // After inner loop:
    //   !found  =>  normal exit  =>  j == |trace|  (exclusion zone = full suffix)
    //    found  =>  break        =>  exists k :: i < k < |trace| && trace[i] < trace[k]

    if !found {
      // All of trace[i+1..] satisfies trace[k] <= trace[i]
      assert forall q :: i < q < |trace| ==> trace[q] <= trace[i];
      // Restate as negated existential — the form the postcondition needs
      assert !(exists k :: i < k < |trace| && trace[i] < trace[k]);
      // 0 <= i < |trace|-1, so i is a concrete counterexample; outer forall fails
      valid := false;
      return;
    }

    // Outer invariant maintained: witness flips p == i from "p >= i" to "exists k"
    i := i + 1;
  }
  // i >= |trace|-1; for every p < |trace|-1 the "p >= i" disjunct is false,
  // so the invariant directly delivers the postcondition — no extra assert needed.
  valid := true;
}
