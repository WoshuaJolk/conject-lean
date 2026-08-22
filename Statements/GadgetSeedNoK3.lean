/-
# The gadget seed does not exist in dimension three

`Statements.CirculantGadgetSeed` (statement 29) claims, for every `k ≥ 2`, a `k × k` matrix with
pairwise orthogonal rows of a common nonzero norm, zero diagonal, and no zero off the diagonal. That
is false at `k = 3`, and this statement is the refutation.

The reason is a counting collapse rather than anything arithmetic. For `i ≠ j`, the pairing of rows
`i` and `j` is `∑ r, conj (M i r) * M j r`, and two of its `k` terms are killed by the zero diagonal:
the `r = i` term contains `M i i = 0` and the `r = j` term contains `M j j = 0`. So the pairing is a
sum of only `k - 2` terms. At `k = 3` that is a *single* term, `conj (M 0 2) * M 1 2` for the pair
`(0, 1)`, and both factors are off-diagonal entries, hence nonzero by hypothesis — so the pairing
cannot vanish and the rows cannot be orthogonal.

This is dimension-specific, and sharp on both sides. At `k = 2` the pairing has zero terms and is
therefore automatically zero, so the gadget exists trivially (`M = [[0,1],[1,0]]`). At `k = 4` the
pairing has two terms, which can cancel, and an explicit real example is the skew-type conference
matrix

```
 0  1  1  1
 1  0  1 -1
 1 -1  0  1
 1  1 -1  0
```

whose rows are pairwise orthogonal with squared norm `3`. So the correct claim is a dichotomy: the
gadget seed exists for `k = 2` and for every `k ≥ 4`, and *only* `k = 3` fails — which is exactly the
dimension where the literature is forced to use a Petersen-based seed instead of two bases plus a
matching, and where the gadget is known to be impossible over the reals. The impossibility here is
over `ℂ`, so it is not a real-arithmetic artifact.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Statements.GadgetSeedNoK3

open scoped BigOperators

/-- The Hermitian pairing of two rows, conjugate-linear in the first argument. -/
abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- In dimension three there is no matrix with zero diagonal, every off-diagonal entry nonzero, and
pairwise orthogonal rows of a common nonzero norm. -/
abbrev statement : Prop :=
  ¬ ∃ (M : Fin 3 → Fin 3 → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0)

theorem target : statement := sorry

end Statements.GadgetSeedNoK3
