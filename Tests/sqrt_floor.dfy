// Integer square root: largest r such that r*r <= n < (r+1)*(r+1).
// Strategy: binary search on the answer in [0, n].
//
// Invariant picture at each step:
//   lo*lo <= n         (lo is a valid candidate)
//   (hi+1)*(hi+1) > n  (hi+1 is already too large)
//   lo <= hi           (search space non-empty)
// Exit (lo == hi): both conditions hold for r = lo = hi.

method SqrtFloor(n: nat) returns (r: nat)
  ensures r * r <= n < (r + 1) * (r + 1)
{
  var lo: nat := 0;
  var hi: nat := n;

  while lo < hi
    invariant lo <= hi
    invariant lo * lo <= n
    invariant (hi + 1) * (hi + 1) > n
    decreases hi - lo
  {
    // Upper midpoint: guarantees mid > lo when lo < hi,
    // so both branches strictly shrink the search space.
    var mid: nat := lo + (hi - lo + 1) / 2;

    if mid * mid <= n {
      lo := mid;      // mid is a valid candidate; raise the lower bound
    } else {
      hi := mid - 1;  // mid is too large; lower the upper bound
    }
  }

  r := lo;
}
