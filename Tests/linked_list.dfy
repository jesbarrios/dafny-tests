// Recursive algebraic datatype — a value type, not heap-allocated.
// No 'reads' clause needed anywhere; pattern matching is exhaustive by construction.
datatype List = Nil | Cons(head: int, tail: List)

// Spec: recursive length function Dafny can unfold one step at a time.
function ListLen(l: List): nat {
  match l
  case Nil        => 0
  case Cons(_, t) => 1 + ListLen(t)
}

// Imperative traversal — verify it matches the spec exactly.
method Length(l: List) returns (n: nat)
  ensures n == ListLen(l)
{
  n := 0;
  var cur := l;
  while cur.Cons?
    decreases cur                              // structural size of the datatype
    invariant n + ListLen(cur) == ListLen(l)  // splitting identity
  {
    cur := cur.tail;
    n := n + 1;
  }
}

// ── Bonus: structural properties proved by induction on the datatype ──────────

// Append two lists.
function Append(l: List, r: List): List {
  match l
  case Nil        => r
  case Cons(h, t) => Cons(h, Append(t, r))
}

// Length distributes over Append: |l ++ r| == |l| + |r|
lemma AppendLen(l: List, r: List)
  ensures ListLen(Append(l, r)) == ListLen(l) + ListLen(r)
{
  match l
  case Nil        => {}
  case Cons(_, t) => { AppendLen(t, r); }
}

// Append is associative.
lemma AppendAssoc(a: List, b: List, c: List)
  ensures Append(Append(a, b), c) == Append(a, Append(b, c))
{
  match a
  case Nil        => {}
  case Cons(_, t) => { AppendAssoc(t, b, c); }
}

// Nil is a right identity for Append.
lemma AppendNilRight(l: List)
  ensures Append(l, Nil) == l
{
  match l
  case Nil        => {}
  case Cons(_, t) => { AppendNilRight(t); }
}
