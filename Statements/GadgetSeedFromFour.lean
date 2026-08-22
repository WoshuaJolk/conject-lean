/-
# The gadget seed exists in every dimension from four on

This is the corrected form of `Statements.CirculantGadgetSeed` (statement 29), which asserted the
same existence for every `k ≥ 2` and is false at `k = 3` (see `Statements.GadgetSeedNoK3`): there the
pairing of two distinct rows collapses to a single product of two off-diagonal entries, which the
hypotheses force to be nonzero.

The claim: for every `k ≥ 4` there is a `k × k` complex matrix with pairwise orthogonal rows of a
common nonzero norm, zero diagonal, and no zero off the diagonal. Together with the standard basis
this is the two-bases-plus-matching gadget with exactly the intended orthogonality graph — two
disjoint `K_k`'s plus the perfect matching `e_i ⟂ M i`, and no accidental edge, since
`⟪e_i, M j⟫ = M j i`.

Evidence, all exact:

* `k = 4`: the skew-type conference matrix with `0` diagonal and `±1` off it, rows orthogonal with
  squared norm `3`. Real, and integral.
* `k = 5, …, 11`: a circulant construction, with no search. The DFT diagonalizes circulants, so
  orthogonal equal-norm rows means unimodular eigenvalues and the diagonal entry is their average;
  hence what is needed is a vanishing sum of `k` unimodular numbers whose remaining Fourier
  coefficients are all nonzero. Roots of unity give the vanishing sum in every dimension, since
  `k = 2a + 3b` for `k ≥ 2` while `{1,-1}` and the cube roots each sum to zero. Certified by
  reduction to `F_p` with `p ≡ 1 mod N` at two primes per dimension.

The assignment of the vanishing sum to frequencies matters and is the reason this is not a
triviality: at `k = 9` the all-cube-roots assignment leaves minors vanishing, and another assignment
does not; at `k = 6` a sixth-root assignment is needed. Not claimed here: tightness, or
`(k+1)`-spanning, which are separate conditions certified for `k = 5, …, 11` but not proved general
in `k`.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Statements.GadgetSeedFromFour

open scoped BigOperators

/-- The Hermitian pairing of two rows, conjugate-linear in the first argument. -/
abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- For every `k ≥ 4` the two-bases-plus-matching gadget seed exists in dimension `k`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0)

theorem target : statement := sorry

end Statements.GadgetSeedFromFour
