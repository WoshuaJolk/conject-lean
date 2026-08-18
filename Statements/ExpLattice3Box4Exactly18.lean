import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# ExpLattice3Box4Exactly18 — the exponent box `{0,…,4}³` maxes out at exactly 18

Every empty polytope of `L₃(2) = {2ⁿ : n ∈ ℕ₀}³` all of whose exponents are at most `4` has
at most 18 vertices, and 18 is attained.

This is the fourth term of a sequence that IS the open problem.  Write `f(M)` for the
maximum number of vertices of an empty polytope of `L₃(2)` with all exponents at most `M`.
Every empty polytope lies in some such box, and `f` is non-decreasing, so

    h(L₃(2)) = sup_M f(M),

and `h(L₃(2)) < ∞` — the root of this problem — holds precisely when `f` is eventually
constant.  Each `f(M)` is therefore a certified lower bound on `h(L₃(2))`, and the
*increments* of `f` are the thing to watch.

Computed exhaustively, in exact integer arithmetic:

    f(1) = 8    (the unit cell {1,2}³, matching h ≥ 2^d)
    f(2) = 12
    f(3) = 15
    f(4) = 18

The search is complete, not heuristic, and what makes it so is
`EmptyPolytopeFourPointCriterion`, filed alongside: emptiness is decided by the subsets of
size at most four, so a finite grid gives a finite hypergraph whose maximum independent set
can be enumerated.

**Status: measurement-grade, not machine-checked.**  The upper half is an 86-million-node
exhaustive search; it is reproducible from the source recorded in this statement's message,
but it is not a kernel-checked proof and nothing here claims it is.  The lower half is
machine-checked separately as `ExpLattice3Base2At18`, whose 18-vertex witness lies in this
box and was independently rediscovered by this search.
-/

namespace Statements.ExpLattice3Box4Exactly18

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- The part of `L₃(2)` with every exponent at most `M`. -/
def box (M : ℕ) : Set (Fin 3 → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, n ≤ M ∧ x i = (2 : ℝ) ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- The maximum number of vertices of an empty polytope of `L₃(2)` with all exponents at
most `4` is exactly 18. -/
abbrev statement : Prop :=
  (∃ V : Set (Fin 3 → ℝ),
      V ⊆ box 4 ∧ IsEmptyPolytope (expLattice 3 2) V ∧ V.ncard = 18) ∧
  (∀ V : Set (Fin 3 → ℝ),
      V ⊆ box 4 → IsEmptyPolytope (expLattice 3 2) V → V.ncard ≤ 18)

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice3Box4Exactly18
