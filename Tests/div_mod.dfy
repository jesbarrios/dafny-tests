// Integer division by repeated subtraction.
//
// Algorithm: start with (q, r) = (0, a) and subtract b from r,
// incrementing q, until r < b.
//
// Invariant picture at each step:
//   a  ==  q * b  +  r        (q * b already "accounted for")
//   r >= b                    (loop guard: can subtract at least once more)
// Exit (r < b): both conditions hold, giving the Euclidean division spec.

method Divide(a: nat, b: nat) returns (q: nat, r: nat)
  requires b > 0
  ensures a == q * b + r
  ensures r < b
{
  q := 0;
  r := a;

  while r >= b
    invariant a == q * b + r
    decreases r
  {
    r := r - b;
    q := q + 1;
  }
}
