import Mathlib

/-!
# ExpLattice3Base3At20 — a 20-vertex empty polytope in `L₃(2)`

`h(L₃(3)) ≥ 20`, where `L₃(3) = {3 ^ n : n ∈ ℕ₀}³ ⊆ ℝ³` and `h` is the maximum number of
vertices of a convex polytope with vertices in the lattice that contains no lattice point
other than its vertices (Ambrus–Balko–Frankl–Jung–Naszódi, European J. Combin. **116**
(2024) 103884).  By Hoffman's proposition (ABFJN Proposition 1) this is `H(L₃(3)) ≥ 20`.

This is the first explicit three-dimensional exponential-lattice configuration recorded at a
base other than `2`.  The only bound in print at a general base `a ≥ 2` is `h(L₃(a)) ≥ 10`,
from the product bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di Summa, Theorem 2.6 of De
Loera–La Haye–Oliveros–Roldán-Pensado, Adv. Geom. 17 (2017) 473–482) together with
`h(L₂(a)) = 5` for `a ≥ 2` (ABFJN Corollary 4).  The vertex set was found by a randomised
plateau search over the exponent box `{0, …, 12}³` and verified in exact integer arithmetic;
its coordinate bounding box is `{0,…,12} × {0,…,11} × {0,…,12}`.

The definitions are the same as in the root statement `ExpLatticeHellyFinite`, restated
here so that this module is self-contained.
-/

namespace Statements.ExpLattice3Base3At20

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- There is an empty polytope with 20 vertices in `L₃(3)`; equivalently `h(L₃(3)) ≥ 20`. -/
abbrev statement : Prop :=
  ∃ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 3) V ∧ V.ncard = 20

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice3Base3At20
