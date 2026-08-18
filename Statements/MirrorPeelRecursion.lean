import Commons.SetPairSystem

/-!
# MirrorPeelRecursion — peeling one unit off the `a` side costs a factor `b`

The mirror image of DualPeelRecursion.  Every `(a+1, b)`-bounded 1-cross intersecting set
pair system of size `m` contains an `(a, b)`-bounded one of some size `m'` with

    m ≤ b * m' + 1.

Proof: swapping the two families of a 1-cross intersecting SPS exchanges the two budgets
(`|A_i ∩ B_j| = 1` for `i ≠ j` is symmetric in the ordered pair, and `A_i ∩ B_i = ∅` is
symmetric outright), so this is DualPeelRecursion applied to `(B, A)` and swapped back.

Concretely, the surviving subsystem is `S_e = {i | e ∈ A i}` for a largest such fibre, with
`e` deleted from every `A i`: on `S_e` every `A i` contains `e`, and `e ∈ A i` forces
`e ∉ B i`, so `e` was never the witness in any `A i ∩ B i'` inside the fibre.

Together the two peels bound the two restriction operations a search over small cases needs:
`|S_e| ≤ m(a-1, b, 1)` and `|T_e| ≤ m(a, b-1, 1)`.  Those are exactly the column caps that
make an exhaustive search over `(a,b)`-bounded systems tractable — for instance at
`(a,b) = (3,4)` they read `|S_e| ≤ m(2,4,1) = 9` and `|T_e| ≤ m(3,3,1) = 10`.

As with DualPeelRecursion this does NOT move the squeeze: iterating the two peels gives
`m(n,n,1) ≤ n^(n+O(1))`, worse than Bollobás for every `n ≥ 2`.
-/

namespace Statements.MirrorPeelRecursion

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (a b m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS (a + 1) b m A B →
      ∃ (m' : ℕ) (A' B' : Fin m' → Finset ℕ),
        Commons.OneCrossSPS a b m' A' B' ∧ m ≤ b * m' + 1

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.MirrorPeelRecursion
