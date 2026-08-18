import Commons.SetPairSystem

/-!
# DualPeelRecursion — peeling one unit off the `b` side costs a factor `a`

Every `(a, b+1)`-bounded `1`-cross intersecting set pair system of size `m` contains an
`(a, b)`-bounded one of some size `m'` with

    m ≤ a * m' + 1.

Proof: fix an index `i`.  The fibres `T e = {j | e ∈ B j}` for `e ∈ A i` partition
`Fin m \ {i}` (FibreCountIdentity), and there are at most `a` of them, so the largest has
`|T e| ≥ (m-1)/a`.  On that fibre every `B j` contains `e`, so deleting `e` from every
`B j` leaves an `(a, b)`-bounded system; and it leaves the cross conditions untouched,
because `e ∈ B j` forces `e ∉ A j`, so `e` was never the witness in any `A j ∩ B j'`
with `j, j'` in the fibre.

HONEST SCOPE.  This does NOT move the squeeze.  Iterating it (and its mirror image) gives
`m(n,n,1) ≤ n^(n+O(1))`, which is worse than Bollobás' `C(2n,n)` for every `n ≥ 2`; the
loss is that `m - 1 = ∑_{e ∈ A i} |T e|` is bounded by `a · max`, whereas in the pentagon
power the fibre sizes decay geometrically (`2m/5, 2m/25, …`) and the sum is dominated by
its largest term.  What the statement supplies is the structural engine in the shape the
page's residual asks for — a passage from budget `(a, b+1)` to budget `(a, b)` with an
explicit multiplicative constant — together with the exact place where the constant is
lossy.  Closing the gap between the constant `a` proved here and the constant `√5` the
conjecture needs is precisely the open content of StepTwoRecursion.
-/

namespace Statements.DualPeelRecursion

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (a b m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS a (b + 1) m A B →
      ∃ (m' : ℕ) (A' B' : Fin m' → Finset ℕ),
        Commons.OneCrossSPS a b m' A' B' ∧ m ≤ a * m' + 1

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.DualPeelRecursion
