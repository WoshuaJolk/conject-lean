import Mathlib

/-!
# ExpLattice3Base2At18 — an 18-vertex empty polytope in `L_3(2)`

`h(L_3(2)) ≥ 18`, where `L_3(2) = {2 ^ n : n ∈ ℕ₀}^3 ⊆ ℝ^3` and `h` is the maximum number
of vertices of a convex polytope with vertices in the lattice containing no lattice point
other than its vertices (Ambrus–Balko–Frankl–Jung–Naszódi, European J. Combin. **116**
(2024) 103884; by Hoffman's proposition this is the Helly number `H(L_3(2))`).

Prior published record: **10**, from the product bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)`
(Conforti–Di Summa, stated as Theorem 2.6 of De Loera–La Haye–Oliveros–Roldán-Pensado,
Adv. Geom. **17** (2017) 473–482, and without a dimension restriction as Proposition 1.5
of Arun, MIT PRIMES 2023) together with `h(L_2(2)) = 5` (ABFJN Corollary 4).  The only
*explicitly written* three-dimensional construction in the literature has 3 vertices
(Arun–Dillon, arXiv:2409.07262 Theorem 1.2, at `α = 2`).

The definitions are the same as in the root statement `ExpLatticeHellyFinite`, restated
here so that this module is self-contained.
-/

namespace Statements.ExpLattice3Base2At18

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- There is an empty polytope with 18 vertices in `L_3(2)`; equivalently
`h(L_3(2)) ≥ 18`, and `H({2 ^ n : n ∈ ℕ₀}^3) ≥ 18`. -/
abbrev statement : Prop :=
  ∃ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 2) V ∧ V.ncard = 18

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice3Base2At18
