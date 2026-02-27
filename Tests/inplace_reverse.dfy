// In-place reversal: swap the outermost pair, then recurse inward.
//
// Spec function (same definition as seq_reverse.dfy):
//   Reverse([]) = []
//   Reverse([x] + s) = Reverse(s) + [x]

function Reverse(s: seq<int>): seq<int> {
  if s == [] then [] else Reverse(s[1..]) + [s[0]]
}

// ── Lemmas needed to connect the loop to the spec ─────────────────────────────

lemma ReverseLen(s: seq<int>)
  ensures |Reverse(s)| == |s|
{
  if s != [] { ReverseLen(s[1..]); }
}

// Element i of Reverse(s) is element (|s|-1-i) of s.
lemma ReverseIndex(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures |Reverse(s)| == |s|
  ensures Reverse(s)[i] == s[|s| - 1 - i]
{
  ReverseLen(s);
  ReverseLen(s[1..]);
  if i < |s| - 1 {
    // Reverse(s)[i] = (Reverse(s[1..]) + [s[0]])[i]
    //              = Reverse(s[1..])[i]           (i < |s[1..]| = |s|-1)
    //              = s[1..][|s|-2-i]              (IH)
    //              = s[|s|-1-i]                   (s[1..][k] = s[k+1])
    ReverseIndex(s[1..], i);
  }
  // i == |s|-1:
  // Reverse(s)[|s|-1] = (Reverse(s[1..]) + [s[0]])[|s|-1] = s[0]
  // s[|s|-1-(|s|-1)] = s[0]  ✓
}

// ── Method ────────────────────────────────────────────────────────────────────

// Two-pointer reversal: lo sweeps up, hi sweeps down, swapping at each step.
//
// Invariant picture:
//   | done (reversed) |    untouched    | done (reversed) |
//   0                lo               hi+1            a.Length
//
// Done zones: a[k] == old(a[a.Length-1-k])  for k < lo and k > hi.
// Middle zone: a[k] == old(a[k])             for lo <= k <= hi.
// The sum lo + hi == a.Length - 1 is preserved, so the zones grow symmetrically.

method ReverseInPlace(a: array<int>)
  modifies a
  ensures a[..] == Reverse(old(a[..]))
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var lo: int := 0;
  var hi: int := a.Length - 1;

  while lo < hi
    invariant 0 <= lo <= a.Length
    invariant hi == a.Length - 1 - lo
    invariant forall k :: 0 <= k < lo       ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: hi < k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: lo <= k <= hi     ==> a[k] == old(a[k])
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases hi - lo
  {
    a[lo], a[hi] := a[hi], a[lo];
    lo := lo + 1;
    hi := hi - 1;
  }

  // Exit: lo >= hi.  Both done-zones together cover all of [0, a.Length).
  // ReverseIndex bridges each element to Reverse(old(a[..]))[k];
  // sequence extensionality then closes a[..] == Reverse(old(a[..])).
  ReverseLen(old(a[..]));
  forall k | 0 <= k < a.Length
    ensures a[k] == Reverse(old(a[..]))[k]
  {
    ReverseIndex(old(a[..]), k);
    if lo <= k && k <= hi {
      // Only reachable when lo == hi == k (middle element of odd-length array).
      // hi == a.Length-1-lo  and  lo == k  ==>  a.Length-1-k == k.
      assert k == a.Length - 1 - k;
    }
  }
}
