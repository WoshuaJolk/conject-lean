import Mathlib

/-!
# ExpLatticeGeoProgAtMost4 — geometric progressions stop at four vertices

A *geometric progression* in the exponential lattice `L₃(2) = {2ⁿ : n ∈ ℕ₀}³` is a set
`{p, p·r, p·r², …}` with the product taken coordinatewise and every coordinate of the ratio
`r` a (possibly negative) power of two.  Equivalently, in exponent coordinates it is an
arithmetic progression: a set of collinear points of `ℤ³`.

This is the natural first construction for the root problem, because it makes convex
position free.  Writing `pₙ = p · rⁿ`, coordinatewise AM–GM gives
`pₙ = √(pₙ₋₁ · pₙ₊₁) ≤ (pₙ₋₁ + pₙ₊₁)/2`, so the points lie on a convex curve and every one
of them is a vertex of the hull, for every ratio and every length.  Only emptiness can fail
— and this statement says it always does, from the fifth term on.

The claim is that no five-term geometric progression with `|log₂ rᵢ| ≤ 6` is an empty
polytope of `L₃(2)`.  Since a subset of an empty polytope is an empty polytope, the
maximum length of an empty geometric progression in that range is therefore at most 4, and
4 is attained (for instance by the ratio `(2⁻¹, 2, 2²)`).

This strictly extends `ExpLatticeScalingBarrier`, which is the case `r = a^{1_S}`, i.e.
`log₂ r ∈ {0,1}³`, and gives 2 rather than 4 there; the present statement covers every
integer ratio exponent up to 6 in absolute value.
-/

namespace Statements.ExpLatticeGeoProgAtMost4

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- The `k`-term geometric progression with first term `p` and coordinatewise ratio `r`. -/
def geoProg (k : ℕ) (p r : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  (fun n : ℕ => fun i => p i * r i ^ n) '' {n : ℕ | n < k}

/-- No five-term geometric progression whose ratio has integer base-two exponents of
absolute value at most 6 is an empty polytope of `L₃(2)`. -/
abbrev statement : Prop :=
  ∀ p r : Fin 3 → ℝ,
    (∀ i, ∃ m : ℤ, m.natAbs ≤ 6 ∧ r i = (2 : ℝ) ^ m) →
    (∃ i, r i ≠ 1) →
    ¬ IsEmptyPolytope (expLattice 3 2) (geoProg 5 p r)

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLatticeGeoProgAtMost4
