// Binary tree — algebraic datatype, value type, no heap allocation.
datatype Tree = Leaf | Node(left: Tree, val: int, right: Tree)

function Max(a: nat, b: nat): nat {
  if a >= b then a else b
}

// ── Spec functions ────────────────────────────────────────────────────────────

// Height = 0 for Leaf; 1 + max(left, right) for Node.
function TreeHeight(t: Tree): nat {
  match t
  case Leaf          => 0
  case Node(l, _, r) => 1 + Max(TreeHeight(l), TreeHeight(r))
}

// Number of internal nodes (not leaves).
function TreeSize(t: Tree): nat {
  match t
  case Leaf          => 0
  case Node(l, _, r) => 1 + TreeSize(l) + TreeSize(r)
}

// Mirror swaps left and right children at every level.
function Mirror(t: Tree): Tree {
  match t
  case Leaf          => Leaf
  case Node(l, v, r) => Node(Mirror(r), v, Mirror(l))
}

// ── Imperative method ─────────────────────────────────────────────────────────

// Recursive method verified against TreeHeight.
// 'decreases t' uses the datatype's built-in structural ordering.
method Height(t: Tree) returns (h: nat)
  ensures h == TreeHeight(t)
  decreases t
{
  match t {
    case Leaf => {
      h := 0;
    }
    case Node(l, _, r) => {
      var lh := Height(l);
      var rh := Height(r);
      h := 1 + (if lh >= rh then lh else rh);
    }
  }
}

// ── Structural lemmas ─────────────────────────────────────────────────────────

// Height is bounded above by the number of nodes.
lemma HeightLeSize(t: Tree)
  ensures TreeHeight(t) <= TreeSize(t)
{
  match t {
    case Leaf          => {}
    case Node(l, _, r) => { HeightLeSize(l); HeightLeSize(r); }
  }
}

// Each subtree is strictly shallower than its parent.
lemma SubtreeHeightLt(t: Tree)
  requires t.Node?
  ensures TreeHeight(t.left)  < TreeHeight(t)
  ensures TreeHeight(t.right) < TreeHeight(t)
{}

// Max is commutative.
lemma MaxComm(a: nat, b: nat)
  ensures Max(a, b) == Max(b, a)
{}

// Mirroring a tree preserves its height.
lemma MirrorHeight(t: Tree)
  ensures TreeHeight(Mirror(t)) == TreeHeight(t)
{
  match t {
    case Leaf          => {}
    case Node(l, _, r) => {
      MirrorHeight(l);
      MirrorHeight(r);
      MaxComm(TreeHeight(r), TreeHeight(l));
    }
  }
}

// Mirroring twice is the identity.
lemma MirrorInvolution(t: Tree)
  ensures Mirror(Mirror(t)) == t
{
  match t {
    case Leaf          => {}
    case Node(l, _, r) => { MirrorInvolution(l); MirrorInvolution(r); }
  }
}
