// ghost_history.dfy
//
// Demonstrates ghost variable history tracking with old() semantics.
//
// Why a ghost FIELD instead of a local ghost var?
//   old(expr) works on heap state at method entry.
//   Local ghost variables are stack-allocated value copies — they do not
//   have a "before" heap snapshot, so old(localVar) is not meaningful in
//   postconditions.  A ghost field lives on the heap, so the verifier can
//   snapshot it with old() at method entry and compare with its value at exit.
//
// Rule: every statement that writes to the declared frame must be flanked
// by ghost updates that record the before- and after-values.  Omitting any
// ghost update prevents Dafny from verifying the postcondition.

class ArrayHistory {

  ghost var history: seq<int>   // full log of (value-before, value-after) per write

  constructor()
    ensures history == []
  {
    history := [];
  }

  // ─── Single increment ──────────────────────────────────────────────────────
  //
  // Appends exactly two entries to history per call:
  //   [old(a[i])]  — the value a[i] held  BEFORE the write
  //   [a[i]]       — the value a[i] holds AFTER  the write
  //
  // modifies this : required because updating the ghost field changes heap state
  // modifies a    : required because the method writes a[i]
  //
  method Increment(a: array<int>, i: int)
    modifies this, a
    requires 0 <= i < a.Length
    ensures history == old(history) + [old(a[i])] + [a[i]]
    ensures a[i]    == old(a[i]) + 1
    ensures forall j :: 0 <= j < a.Length && j != i ==> a[j] == old(a[j])
  {
    // Ghost update (pre-write): record the value a[i] is about to lose.
    // Must precede the real write so a[i] still holds old(a[i]).
    history := history + [a[i]];

    // ── real modification ────────────────────────────────────────────────────
    a[i] := a[i] + 1;

    // Ghost update (post-write): record the new value of a[i].
    // Omitting this leaves history one entry short → ensures fails.
    history := history + [a[i]];
  }

  // ─── Double increment ──────────────────────────────────────────────────────
  //
  // Shows that EVERY write needs its own flanking ghost updates, not just the
  // first and last.  Removing any of the four ghost statements causes a
  // verification failure, because the verifier loses the intermediate value.
  //
  // History log after the call (let v = old(a[i])):
  //
  //   old(history) + [v] + [v+1] + [v+1] + [v+2]
  //                  ^       ^       ^       ^
  //               pre-1  post-1  pre-2  post-2
  //
  // Note: post-1 and pre-2 are the same value (v+1) because no other code
  // runs between them; they are kept separate so each write has its own pair.
  //
  method IncrementTwice(a: array<int>, i: int)
    modifies this, a
    requires 0 <= i < a.Length
    ensures history == old(history)
                     + [old(a[i])]
                     + [old(a[i]) + 1]
                     + [old(a[i]) + 1]
                     + [a[i]]
    ensures a[i] == old(a[i]) + 2
    ensures forall j :: 0 <= j < a.Length && j != i ==> a[j] == old(a[j])
  {
    // ── first write ──────────────────────────────────────────────────────────
    history := history + [a[i]];   // ghost: before first write  (v)
    a[i] := a[i] + 1;
    history := history + [a[i]];   // ghost: after  first write  (v+1)

    // ── second write ─────────────────────────────────────────────────────────
    history := history + [a[i]];   // ghost: before second write (v+1)
    a[i] := a[i] + 1;
    history := history + [a[i]];   // ghost: after  second write (v+2)
  }
}
