import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

/-!
# CoordinateUniformGL — invertible basis change yields coordinate uniformity

Companion residual of `UniformSecondBlockPlacement` (jig.so/p/14?s=24). That statement takes
coordinate uniformity of the second block as a hypothesis and produces a phase placement. What it
does *not* supply is a transform that puts an actual seed into coordinate-uniform position. This
statement is that missing front, for every `k ≥ 2`.

## The argument

Fix a finite family `v₁, …, v_m` of nonzero vectors in `ℂ^k` and let `U` range over `GL(k)`. Every
minor needed for coordinate uniformity is a polynomial in the entries of `U`, and there are only
finitely many of them (`m` is finite). By irreducibility of `GL(k)`, the whole conjunction holds on
a dense open set as soon as no single one of those polynomials is identically zero. Check each
type:

* a `1 × 1` minor is `(Uv_i)_r`, not identically zero because `v_i ≠ 0`;
* an `r × r` minor on an independent selection `S` is, up to determinant factors, a Plücker
  coordinate of `U · (∧_{i∈S} v_i)`, and `∧ v_i ≠ 0` precisely because `S` is independent, so it
  is not identically zero either;
* the top minor on an independent `k`-set is `det(U) · det(v_S) ≠ 0` outright for invertible `U`.

Tightness and `(k+1)`-spanning do no work in this proof: independent selections already supply the
nonvanishing wedge that each minor polynomial needs, so nonzero vectors suffice. Nothing in the
argument mentions the ambient dimension beyond `k`, so the statement is uniform in `k`.

## The independent-selection exemption

Coordinate uniformity asks the minor condition only of *linearly independent* selections — same
convention as `UniformSecondBlockPlacement`. That restriction is essential rather than cosmetic: in
a `k`-regular orthogonality graph the `k` neighbours of a vertex are dependent, so their full-size
minors vanish under every invertible change of basis. If the definition quantified over *all*
selections rather than independent ones, the statement would be false for a degenerate seed, and
the whole construction would turn on this clause.

Scope. Only the existence of some invertible linear transform — not a specific matrix, not
unitarity, not the orthogonality graph. Nothing is claimed for `k = 1`.
-/

namespace Statements.CoordinateUniformGL

open Matrix

variable {k : ℕ}

/-- Coordinate uniformity: every linearly independent selection of `t` vectors has a nonzero minor
on every choice of `t` coordinates. Dependent selections are exempt — same convention as
`UniformSecondBlockPlacement`. -/
abbrev CoordinateUniform {n : ℕ} (w : Fin n → Fin k → ℂ) : Prop :=
  ∀ (t : ℕ) (b : Fin t → Fin n) (e : Fin t → Fin k),
    Function.Injective b → Function.Injective e →
    LinearIndependent ℂ (fun p => w (b p)) →
    Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0

/-- Apply a `k × k` matrix to a coordinate vector. -/
abbrev applyMat (U : Matrix (Fin k) (Fin k) ℂ) (x : Fin k → ℂ) : Fin k → ℂ :=
  U.mulVec x

/-- The canonical proposition.

For every `k ≥ 2` and every finite family of nonzero vectors in `ℂ^k`, some invertible linear
transform puts the family into coordinate-uniform position. Combined with
`UniformSecondBlockPlacement`, that supplies the second-block input of the copies genericity half
for every `k`. -/
abbrev statement : Prop :=
  ∀ (k n : ℕ), 2 ≤ k →
    ∀ (v : Fin n → Fin k → ℂ),
      (∀ i, v i ≠ 0) →
      ∃ U : Matrix (Fin k) (Fin k) ℂ,
        IsUnit U.det ∧
        CoordinateUniform (fun i => applyMat U (v i))

theorem target : statement := sorry

end Statements.CoordinateUniformGL
