// ── Built-in + operator ───────────────────────────────────────────────────────
// Dafny's sequence axioms give these for free; stating them makes the contract
// explicit and lets other files use them as named lemmas.

lemma LengthAppend<T>(s: seq<T>, t: seq<T>)
  ensures |s + t| == |s| + |t|
{}

lemma AppendAssocBuiltin<T>(s: seq<T>, t: seq<T>, u: seq<T>)
  ensures (s + t) + u == s + (t + u)
{}

lemma AppendNilLeftBuiltin<T>(s: seq<T>)
  ensures [] + s == s
{}

lemma AppendNilRightBuiltin<T>(s: seq<T>)
  ensures s + [] == s
{}

// ── Recursive Append function ─────────────────────────────────────────────────
// Defined structurally on s, peeling from the front.  Requires induction to
// prove any non-trivial property.

function Append<T>(s: seq<T>, t: seq<T>): seq<T> {
  if s == [] then t else [s[0]] + Append(s[1..], t)
}

// Append(s, t) == s + t  (bridges custom function to built-in operator)
lemma AppendEquiv<T>(s: seq<T>, t: seq<T>)
  ensures Append(s, t) == s + t
{
  if s != [] {
    AppendEquiv(s[1..], t);
  }
}

// |Append(s, t)| == |s| + |t|
lemma AppendLength<T>(s: seq<T>, t: seq<T>)
  ensures |Append(s, t)| == |s| + |t|
{
  if s != [] {
    AppendLength(s[1..], t);
  }
}

// [] is a left identity: Append([], s) == s
lemma AppendNilLeft<T>(s: seq<T>)
  ensures Append([], s) == s
{}  // base case of the definition; no induction needed

// [] is a right identity: Append(s, []) == s
lemma AppendNilRight<T>(s: seq<T>)
  ensures Append(s, []) == s
{
  if s != [] {
    AppendNilRight(s[1..]);
  }
}

// Append is associative: Append(Append(s, t), u) == Append(s, Append(t, u))
lemma AppendAssoc<T>(s: seq<T>, t: seq<T>, u: seq<T>)
  ensures Append(Append(s, t), u) == Append(s, Append(t, u))
{
  if s != [] {
    AppendAssoc(s[1..], t, u);
  }
}
