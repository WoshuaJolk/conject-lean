import Mathlib

/-!
# ExpLatticeLevelReduction — the root reduces to bounding the number of levels

For a base `α`, write `L_d(α) = {α ⁿ : n ∈ ℕ₀}^d ⊆ ℝ^d` and call a finite `V ⊆ L_d(α)` an
*empty polytope* when every point of `V` is a vertex of `conv V` and `conv V` meets
`L_d(α)` only inside `V` (Ambrus–Balko–Frankl–Jung–Naszódi).  A *level* of `V ⊆ L₃(α)` is a
value taken by the first coordinate, so the number of levels of `V` is
`((fun v => v 0) '' V).ncard`.

This statement says two things.

* **Slice bound.**  `V.ncard ≤ N · (number of levels of V)` whenever `N` bounds the number
  of vertices of every empty polytope of the *planar* lattice `L₂(α)`.  The mechanism is
  that each level set of `V`, viewed in the plane by forgetting the first coordinate, is
  itself an empty polytope of `L₂(α)`.
* **Finiteness transfer.**  Consequently, if the planar Helly number is finite (which is
  ABFJN Theorem 1, for every `α > 1`) and the number of levels is bounded by some `K`, then
  `h(L₃(α)) ≤ N · K < ∞`.

So the root `ExpLatticeHellyFinite` — is `h(L₃(α))` finite — is *equivalent*, given ABFJN,
to the question whether an empty polytope of `L₃(α)` can have arbitrarily many distinct
first coordinates.  The converse direction is immediate, since the number of levels never
exceeds the number of vertices.

Nothing here is specific to the base: `α` is an arbitrary real.  The dimensions 3 and 2 are
the only ones used, but the same proof gives `d` and `d - 1`.
-/

namespace Statements.ExpLatticeLevelReduction

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- The slice bound, and the finiteness transfer it gives. -/
abbrev statement : Prop :=
  (∀ α : ℝ, ∀ N : ℕ,
      (∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N) →
      ∀ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 α) V →
        V.ncard ≤ N * ((fun v : Fin 3 → ℝ => v 0) '' V).ncard) ∧
  (∀ α : ℝ, ∀ N K : ℕ,
      (∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N) →
      (∀ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 α) V →
          ((fun v : Fin 3 → ℝ => v 0) '' V).ncard ≤ K) →
      ∀ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 α) V → V.ncard ≤ N * K)

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLatticeLevelReduction
