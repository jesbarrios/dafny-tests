function SumSeq(s: seq<int>): int {
  if s == [] then 0 else s[0] + SumSeq(s[1..])
}

lemma SumSeqAppend(s: seq<int>, x: int)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
{
  if s != [] {
    assert (s + [x])[1..] == s[1..] + [x];
    SumSeqAppend(s[1..], x);
  }
}

// "Optimized": unroll the loop body 2x so both additions are independent —
// no data dependency between a[i] and a[i+1], exploiting instruction-level parallelism.
method ArraySum(a: array<int>) returns (sum: int)
  ensures sum == SumSeq(a[..])
{
  sum := 0;
  var i := 0;
  while i + 1 < a.Length
    invariant 0 <= i <= a.Length
    invariant sum == SumSeq(a[..i])
  {
    SumSeqAppend(a[..i], a[i]);
    assert a[..i] + [a[i]] == a[..i + 1];
    SumSeqAppend(a[..i + 1], a[i + 1]);
    assert a[..i + 1] + [a[i + 1]] == a[..i + 2];
    sum := sum + a[i] + a[i + 1];  // process two elements per iteration
    i := i + 2;
  }
  // Bug: when a.Length is odd, the last element a[a.Length-1] is never visited.
  // Loop exits with i == a.Length-1, so sum == SumSeq(a[..a.Length-1]) != SumSeq(a[..])
  assert a[..a.Length] == a[..];
}
