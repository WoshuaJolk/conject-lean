import Mathlib

/-!
# ExpLattice2Base2AtMost5 — the planar ceiling, `h(L₂(2)) ≤ 5`

Ambrus–Balko–Frankl–Jung–Naszódi, *On Helly numbers of exponential lattices*, European J.
Combin. **116** (2024) 103884, Theorem 2: `h(α) ≤ 5` for every `α ≥ 2`; with Theorem 3 this
gives Corollary 4, `h(L₂(α)) = 5` for every `α ≥ 2`.  This module states the upper half at
`α = 2`, which is the half that does work.

Why it is worth a label of its own.  It is the ceiling on every product-type construction
in dimension three.  The product bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di Summa, as
Theorem 2.6 of De Loera–La Haye–Oliveros–Roldán-Pensado, Adv. Geom. **17** (2017) 473–482;
also Averkov–Weismantel Theorem 1.1(2), Garber Corollary 4.5) applied to
`L₃(2) = L₂(2) × {2ⁿ}` yields exactly `2 · h(L₂(2)) = 10` vertices, and by the statement
below it can never yield more.  So the route "improve the three-dimensional lower bound by
stacking two levels of a planar empty polygon" is closed at 10, permanently — while the
best certified value is 19, reached by direct search rather than by any product.

This statement is filed unproved.  It is a published, refereed theorem, and its Lean proof
is a real piece of work (ABFJN's argument orders the edge slopes of an empty polygon and
counts them); nothing here asserts it has been machine-checked.
-/

namespace Statements.ExpLattice2Base2AtMost5

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- `h(L₂(2)) ≤ 5`: every empty polygon of the planar exponential lattice
`{2ⁿ : n ∈ ℕ₀}²` has at most five vertices.  ABFJN Theorem 2 at `α = 2`. -/
abbrev statement : Prop :=
  ∀ V : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 2) V → V.ncard ≤ 5

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice2Base2AtMost5
