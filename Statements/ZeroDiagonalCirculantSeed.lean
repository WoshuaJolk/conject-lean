/-
# Zero-diagonal scaled-unitary circulants exist in every dimension

The degenerate class of a product-basis decomposition cannot be supplied by the
Lovász–Saks–Schrijver theorem: general position is impossible for a `k`-regular class in
dimension `k`, because the `k` neighbours of a vertex all lie in that vertex's orthogonal
complement and are therefore dependent. So that class has to come from an explicit gadget, and the
gadget needed is the *two-bases-plus-matching* one: the standard basis `e_0, …, e_{k-1}` together
with the rows of a `k × k` matrix `M` with

* pairwise orthogonal rows of equal norm (so the rows form a scaled orthogonal basis, giving the
  second clique), and
* zero diagonal (so `e_i` is orthogonal to row `i`, giving the perfect matching, and to no other
  row).

Searches for such an `M` over the Gaussian rationals succeed at `k = 4, 5, 6` and fail at `k = 7, 8`
at every bound tried. The obstruction is the number field, not the dimension: taking `M` circulant,
`M i j = c (j - i)`, the discrete Fourier transform diagonalizes it, so `M` is scaled-unitary
exactly when its eigenvalues are unimodular, and its diagonal entry is the *average of the
eigenvalues*. A zero-diagonal scaled-unitary circulant is therefore exactly **a vanishing sum of `k`
unimodular numbers** — and roots of unity supply one in every dimension, since `k = 2a + 3b` is
solvable for every `k ≥ 2` while `{1, -1}` and `{1, ζ₃, ζ₃²}` both sum to zero.

This statement is that existence, spelled without reference to circulants or to the transform: a
matrix with orthogonal rows of equal nonzero norm and zero diagonal, in every dimension `k ≥ 2`.

The remaining gadget conditions — that every off-diagonal entry is nonzero (no accidental
orthogonality), tightness, and `(k+1)`-spanning — are *not* claimed here. They hold for the
construction above in every dimension checked exactly (`k = 5, …, 11`, certified by reduction to
`F_p` with `p ≡ 1 mod N` at two primes each), but they depend on which vanishing sum is used, and no
proof general in `k` is claimed.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Statements.ZeroDiagonalCirculantSeed

open scoped BigOperators

/-- The Hermitian pairing of two rows, conjugate-linear in the first argument. -/
abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- For every dimension `k ≥ 2` there is a `k × k` complex matrix whose rows are pairwise
orthogonal with a common nonzero squared norm, and whose diagonal vanishes identically.

Together with the standard basis this is the two-bases-plus-matching gadget: the `e_i` form one
orthogonal block, the rows of `M` form another, and `M i i = 0` says exactly that `e_i` is
orthogonal to row `i`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0)

theorem target : statement := sorry

end Statements.ZeroDiagonalCirculantSeed
