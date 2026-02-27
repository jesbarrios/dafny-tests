function Reverse(s: seq<int>): seq<int> {
  if s == [] then [] else Reverse(s[1..]) + [s[0]]
}

// Reverse unfolds from the front: Reverse([x] + s) = Reverse(s) + [x].
// The loop builds from the back, so this lemma bridges the two directions.
lemma ReverseConsAppend(x: int, s: seq<int>)
  ensures Reverse([x] + s) == Reverse(s) + [x]
{
  assert ([x] + s)[1..] == s;  // one unfold of the definition suffices
}

method ReverseArray(a: array<int>) returns (b: array<int>)
  ensures b.Length == a.Length
  ensures b[..] == Reverse(a[..])
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant b[..i] == Reverse(a[a.Length - i..])
  {
    assert a[a.Length - i - 1..] == [a[a.Length - i - 1]] + a[a.Length - i..];
    ReverseConsAppend(a[a.Length - i - 1], a[a.Length - i..]);
    b[i] := a[a.Length - 1 - i];
    i := i + 1;
  }
  assert a[0..] == a[..];
}
