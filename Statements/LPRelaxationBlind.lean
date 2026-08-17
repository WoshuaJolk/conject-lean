import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# LPRelaxationBlind — the fractional biclique-partition relaxation is blind to every `m`

By FGK Theorem 1.8, `m(n,n,1)` is the largest `m` whose off-diagonal `m × m` cells admit an
exact partition into combinatorial rectangles `S × T` with `S ∩ T = ∅` and all row and column
loads at most `n`. Dropping integrality gives a linear program in the rectangle weights.

This statement says the relaxation is FEASIBLE with load strictly below `2` for every even
size `m = 2k`: put weight `1 / C(2k-2, k-1)` on each balanced complementary rectangle
`(S, Sᶜ)` with `|S| = k`. Coverage of every off-diagonal cell is exactly `1` and every row and
column load is exactly `2 - 1/k`.

Consequence, which is the barrier: any upper bound on `m` that is a consequence of the LP —
hence any bound certified by LP duality, by an eigenvalue argument, or by any inequality
linear in the rectangle weights — must already hold for the fractional optimum, and the
fractional optimum has load `< 2` for every `m`. So no such bound separates any `m` at all
once `n ≥ 2`. It cannot even recover Bollobás' `C(2n,n)`. Integrality is load-bearing.
-/

namespace Statements.LPRelaxationBlind

/-- The canonical proposition: for every `k ≥ 1` there is a nonnegative weighting of the
complementary rectangles on `Fin (2*k)` with exact off-diagonal coverage `1` and every row and
column load equal to `2 - 1/k`, which is `< 2`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 0 < k → ∃ w : Finset (Fin (2 * k)) → ℚ,
    (∀ S, 0 ≤ w S) ∧
    (∀ i j : Fin (2 * k), i ≠ j →
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * k)) => i ∈ S ∧ j ∉ S), w S) = 1) ∧
    (∀ i : Fin (2 * k),
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * k)) => i ∈ S), w S)
        = 2 - 1 / (k : ℚ)) ∧
    (∀ j : Fin (2 * k),
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * k)) => j ∉ S), w S)
        = 2 - 1 / (k : ℚ)) ∧
    (2 : ℚ) - 1 / (k : ℚ) < 2

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.LPRelaxationBlind
