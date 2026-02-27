function SumSeq(s: seq<int>): int {
  if s == [] then 0 else s[0] + SumSeq(s[1..])
}

// SumSeq unfolds from the front; this lemma lets the loop accumulate from the back.
lemma SumSeqAppend(s: seq<int>, x: int)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
{
  if s != [] {
    assert (s + [x])[1..] == s[1..] + [x];
    SumSeqAppend(s[1..], x);
  }
}

method ArraySum(a: array<int>) returns (sum: int)
  ensures sum == SumSeq(a[..])
{
  sum := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sum == SumSeq(a[..i])
  {
    SumSeqAppend(a[..i], a[i]);
    assert a[..i] + [a[i]] == a[..i + 1];
    sum := sum + a[i];
    i := i + 1;
  }
  assert a[..a.Length] == a[..];
}
