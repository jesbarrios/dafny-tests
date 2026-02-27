// Flatten: concatenate a sequence of sequences into one flat sequence.
//
// FlattenAssoc: Flatten(a + b) == Flatten(a) + Flatten(b)
//
// Proof strategy: structural induction on |a|.
//   Base  (a == []): [] + b == b, so Flatten(a+b) = Flatten(b) = [] + Flatten(b)
//   Step  (a != []): let head = a[0], tail = a[1..]
//     Key identities:
//       (1) a + b  == [head] + (tail + b)          (sequence arithmetic)
//       (2) Flatten(a + b)  == head + Flatten(tail + b)  (unfold on non-empty seq)
//       (3) Flatten(tail + b) == Flatten(tail) + Flatten(b)  (IH on tail)
//       (4) Flatten(a) == head + Flatten(tail)      (unfold definition of Flatten)
//     Chain: Flatten(a+b) == head + Flatten(tail+b)     by (2)
//                         == head + Flatten(tail) + Flatten(b)  by (3)
//                         == Flatten(a) + Flatten(b)   by (4)

function Flatten(seqs: seq<seq<int>>): seq<int>
  decreases seqs
{
  if seqs == [] then []
  else seqs[0] + Flatten(seqs[1..])
}

lemma FlattenAssoc(a: seq<seq<int>>, b: seq<seq<int>>)
  ensures Flatten(a + b) == Flatten(a) + Flatten(b)
  decreases a
{
  if a == [] {
    // Flatten([] + b) == Flatten(b) == [] + Flatten(b) == Flatten([]) + Flatten(b)
    assert a + b == b;
  } else {
    var head := a[0];
    var tail := a[1..];

    // Inductive hypothesis on the strictly-shorter tail
    FlattenAssoc(tail, b);
    // Now available: Flatten(tail + b) == Flatten(tail) + Flatten(b)

    // (1) Sequence identity so Dafny can unfold Flatten(a+b) correctly
    assert a + b == [head] + (tail + b);

    // (2) Unfold Flatten on the non-empty sequence [head] + (tail + b)
    //     Dafny sees: ([head] + (tail + b))[0] == head
    //                 ([head] + (tail + b))[1..] == tail + b
    assert Flatten(a + b) == head + Flatten(tail + b);

    // (3) Unfold definition of Flatten(a) on the non-empty a
    assert Flatten(a) == head + Flatten(tail);

    // Dafny chains (2) + IH + (3) to conclude the postcondition
  }
}

// ── Sanity checks ──────────────────────────────────────────────────────────

lemma FlattenEmpty()
  ensures Flatten([]) == []
{}

lemma FlattenSingleton(s: seq<int>)
  ensures Flatten([s]) == s
{}

lemma FlattenNilLeft(b: seq<seq<int>>)
  ensures Flatten([] + b) == Flatten(b)
{
  assert [] + b == b;
}

lemma FlattenNilRight(a: seq<seq<int>>)
  ensures Flatten(a + []) == Flatten(a)
{
  FlattenAssoc(a, []);
}

// Three-way associativity: Flatten((a+b)+c) == Flatten(a+(b+c))
// (Both sides equal Flatten(a)+Flatten(b)+Flatten(c) by FlattenAssoc)
lemma FlattenAssoc3(a: seq<seq<int>>, b: seq<seq<int>>, c: seq<seq<int>>)
  ensures Flatten(a + b + c) == Flatten(a) + Flatten(b) + Flatten(c)
{
  FlattenAssoc(a + b, c);   // Flatten((a+b)+c) == Flatten(a+b) + Flatten(c)
  FlattenAssoc(a, b);       // Flatten(a+b)     == Flatten(a)   + Flatten(b)
}
