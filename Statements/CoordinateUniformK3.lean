import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Card

/-!
# CoordinateUniformK3 — the k = 3 template for arranging coordinate uniformity

Companion residual of `UniformSecondBlockPlacement` (jig.so/p/14?s=24). That statement takes
coordinate uniformity of the second block as a hypothesis and produces a phase placement. What it
does *not* supply is a transform that puts an actual seed into coordinate-uniform position. This
statement is that missing front, at `k = 3` — the one place an existing result upgrades for free,
and the template for the general-`k` argument.

## Why k = 3 is free

Lovász–Saks–Schrijver: a graph on `n` vertices has a general-position orthogonal representation in
`ℝ^d` iff it is `(n - d)`-connected. The case `d = 2` — often written `GP(n, 2)` — is the first
nontrivial instance and is classical. At ambient dimension `k = 3`, coordinate uniformity asks
only that

* every nonzero vector has all three coordinates nonzero (`t = 1`),
* every independent pair has all three `2 × 2` minors nonzero (`t = 2`),
* every independent triple has nonzero determinant on every coordinate triple (`t = 3`).

A general-position family in `ℂ^3` already has every triple independent. After a generic change of
basis the coordinate flag is transverse to every relevant subspace, so all those minors are
nonzero: that is exactly coordinate uniformity. The `d = 2` theory upgrades to this `k = 3`
uniformity statement without a new existence argument — only the translation from general position
plus a generic basis change into the minor language of `UniformSecondBlockPlacement`.

## Why it is the template

For general `k` the same pattern applies: LSS supplies general-position orthogonal representations
from `(n - k)`-connectivity; a generic basis change turns general position into coordinate
uniformity; `UniformSecondBlockPlacement` then closes the copies genericity half. The `k = 3`
case is where that pattern can be written and proved first, with the `GP(n, 2)` / `d = 2`
infrastructure as the free input, before the ambient-dimension bookkeeping is generalized.

## Scope

Only `k = 3`. Only the existence of some invertible linear transform making a tight
`(k+1)`-spanning family of nonzero vectors coordinate-uniform — not a specific matrix, not
unitarity, not the orthogonality graph. Degenerate `k`-regular seeds cannot be in *full* general
position (their `k` neighbours are dependent), but coordinate uniformity asks the minor condition
only of *independent* selections, which is compatible with that forced dependence and is what
`UniformSecondBlockPlacement` consumes. Nothing is claimed for `k ≠ 3`; that is the general-`k`
follow-up.
-/

namespace Statements.CoordinateUniformK3

open Matrix

/-- Coordinate uniformity at `k = 3`: every linearly independent selection of `t` vectors has a
nonzero minor on every choice of `t` coordinates. Dependent selections are exempt — same
convention as `UniformSecondBlockPlacement`. -/
abbrev CoordinateUniform (w : Fin n → Fin 3 → ℂ) : Prop :=
  ∀ (t : ℕ) (b : Fin t → Fin n) (e : Fin t → Fin 3),
    Function.Injective b → Function.Injective e →
    LinearIndependent ℂ (fun p => w (b p)) →
    Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0

/-- Apply a `3 × 3` matrix to a coordinate vector. -/
abbrev applyMat (U : Matrix (Fin 3) (Fin 3) ℂ) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  U.mulVec x

/-- Tightness at `k = 3`: every at most `2` vectors are linearly independent. -/
abbrev Tight (v : Fin n → Fin 3 → ℂ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ 2 → LinearIndependent ℂ fun i : (S : Set (Fin n)) => v i

/-- `(k+1)`-spanning at `k = 3`: every `4` vectors span `ℂ^3`. -/
abbrev Spanning (v : Fin n → Fin 3 → ℂ) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 →
    Submodule.span ℂ (Set.range fun i : (S : Set (Fin n)) => v i) = ⊤

/-- The canonical proposition.

For every finite family of nonzero vectors in `ℂ^3` that is tight and `4`-spanning, some
invertible linear transform puts the family into coordinate-uniform position. Combined with
`UniformSecondBlockPlacement`, that supplies the second-block input of the copies genericity
half at `k = 3`. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (v : Fin n → Fin 3 → ℂ),
    (∀ i, v i ≠ 0) → Tight v → Spanning v →
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ,
      IsUnit U.det ∧
      CoordinateUniform (fun i => applyMat U (v i))

theorem target : statement := sorry

end Statements.CoordinateUniformK3
