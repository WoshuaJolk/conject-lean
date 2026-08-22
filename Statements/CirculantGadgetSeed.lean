/-
# The two-bases-plus-matching gadget exists in every dimension

This strengthens `Statements.ZeroDiagonalCirculantSeed` (statement 28), which asked only for
orthogonal equal-norm rows and a vanishing diagonal, and which — as I noticed after filing it — is
satisfied by the cyclic shift permutation matrix and so does not pin down the gadget at all. The
missing condition is that no OTHER pairing vanishes: with

* `A = e_0, …, e_{k-1}` the standard basis, and
* `B = ` the rows of `M`,

the intended orthogonality graph is two disjoint `K_k`'s plus the perfect matching `e_i ⟂ M i`, and
`e_i ⟂ M j` for `i ≠ j` would be an accidental edge, changing the graph and breaking the
decomposition it is meant to realize. Since `⟪e_i, M j⟫ = M j i`, ruling that out is exactly the
requirement that every off-diagonal entry of `M` is nonzero — a permutation matrix fails it
maximally.

So the claim here is: in every dimension `k ≥ 2` there is a `k × k` matrix with pairwise orthogonal
rows of a common nonzero norm, zero diagonal, and *no* zero off the diagonal.

The construction is circulant, `M i j = c (j - i)`. The discrete Fourier transform diagonalizes
circulants, so orthogonal equal-norm rows means unimodular eigenvalues, the diagonal entry is the
average of the eigenvalues, and the off-diagonal entries are the other Fourier coefficients. The
claim is therefore equivalent to: *there are `k` unimodular numbers summing to zero, all of whose
other Fourier coefficients are nonzero.* Roots of unity supply the vanishing sum in every dimension
(`k = 2a + 3b`, with `{1,-1}` and the cube roots each summing to zero), but the nonvanishing of the
remaining coefficients depends on which sum is used and how it is assigned to frequencies: at `k = 9`
the all-cube-roots assignment fails, and another assignment succeeds. What is not claimed here is
tightness or `(k+1)`-spanning of the gadget; those are separate conditions, certified exactly for
`k = 5, …, 11` but not proved general in `k`.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Statements.CirculantGadgetSeed

open scoped BigOperators

/-- The Hermitian pairing of two rows, conjugate-linear in the first argument. -/
abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- For every dimension `k ≥ 2` there is a `k × k` complex matrix whose rows are pairwise orthogonal
with a common nonzero squared norm, whose diagonal vanishes identically, and *none* of whose
off-diagonal entries vanish.

With the standard basis this realizes the two-bases-plus-matching gadget exactly: two disjoint
`K_k`'s, the perfect matching `e_i ⟂ M i` supplied by the zero diagonal, and no accidental edge,
since `⟪e_i, M j⟫ = M j i ≠ 0` for `i ≠ j`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0)

theorem target : statement := sorry

end Statements.CirculantGadgetSeed
