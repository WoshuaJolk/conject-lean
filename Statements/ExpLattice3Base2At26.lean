import Mathlib

/-!
# ExpLattice3Base2At26 — a 26-vertex empty polytope in `L₃(2)`

`h(L₃(2)) ≥ 26`, where `L₃(2) = {2 ^ n : n ∈ ℕ₀}³ ⊆ ℝ³` and `h` is the maximum number of
vertices of a convex polytope with vertices in the lattice that contains no lattice point
other than its vertices (Ambrus–Balko–Frankl–Jung–Naszódi, European J. Combin. **116**
(2024) 103884).  By Hoffman's proposition (ABFJN Proposition 1) this is `H(L₃(2)) ≥ 26`.

This improves the 19-vertex certificate of statement `ExpLattice3Base2At19`, the 18-vertex
certificate of `ExpLattice3Base2At18`, and the prior published record of 10, which comes
from the product bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di Summa, Theorem 2.6 of De
Loera–La Haye–Oliveros–Roldán-Pensado, Adv. Geom. 17 (2017) 473–482) together with
`h(L₂(2)) = 5` (ABFJN Corollary 4).  The vertex set was found by a randomised
plateau search over the exponent box `{0, …, 13}³` and verified in exact integer
arithmetic; it lives, after dividing each coordinate by the largest power of two that
divides every coordinate of that column, in the exponent box `{0,…,12} × {0,…,12} × {0,…,9}`.

The definitions are the same as in the root statement `ExpLatticeHellyFinite`, restated
here so that this module is self-contained.
-/

namespace Statements.ExpLattice3Base2At26

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- There is an empty polytope with 26 vertices in `L₃(2)`; equivalently `h(L₃(2)) ≥ 26`. -/
abbrev statement : Prop :=
  ∃ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 2) V ∧ V.ncard = 26

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice3Base2At26
