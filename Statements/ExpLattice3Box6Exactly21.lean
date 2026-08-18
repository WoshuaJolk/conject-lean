import Mathlib

/-!
# ExpLattice3Box6Exactly21 — the exponent-box maxima of `L₃(2)` at `M = 5` and `M = 6`

Write `f M` for the largest number of vertices of an empty polytope of the exponential
lattice `L₃(2) = {2ⁿ : n ∈ ℕ₀}³` all of whose exponents are at most `M`.  Emptiness is
always with respect to the *whole* lattice, not the box; since `conv V` lies in the
coordinate bounding box of `V`, the two readings agree.

`f` is non-decreasing and `h(L₃(2)) = sup_M f M`, so the root question
`ExpLatticeHellyFinite` — is `h(L₃(2))` finite — is exactly the question whether `f` is
eventually constant, and the increments of `f` are the object of interest.

The previously recorded values are `f 1 = 8`, `f 2 = 12`, `f 3 = 15`, `f 4 = 18`
(`ExpLattice3Box4Exactly18`).  This statement adds the next two:

    f 5 = 19    and    f 6 = 21.

Both were computed by complete enumeration; neither is machine-checked, and no artifact is
filed against this statement.  See `scope` for the method and the controls.
-/

namespace Statements.ExpLattice3Box6Exactly21

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- Every coordinate of every point of `V` is `2 ^ n` for some `n ≤ M`. -/
def InBox (M : ℕ) (V : Set (Fin 3 → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ i, ∃ n : ℕ, n ≤ M ∧ v i = (2 : ℝ) ^ n

/-- `f 5 = 19` and `f 6 = 21`: each bound is attained, and no empty polytope of `L₃(2)`
inside the corresponding exponent box has more vertices. -/
abbrev statement : Prop :=
  (∀ V : Set (Fin 3 → ℝ),
      IsEmptyPolytope (expLattice 3 2) V → InBox 5 V → V.ncard ≤ 19) ∧
  (∃ V : Set (Fin 3 → ℝ),
      IsEmptyPolytope (expLattice 3 2) V ∧ InBox 5 V ∧ V.ncard = 19) ∧
  (∀ V : Set (Fin 3 → ℝ),
      IsEmptyPolytope (expLattice 3 2) V → InBox 6 V → V.ncard ≤ 21) ∧
  (∃ V : Set (Fin 3 → ℝ),
      IsEmptyPolytope (expLattice 3 2) V ∧ InBox 6 V ∧ V.ncard = 21)

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice3Box6Exactly21
