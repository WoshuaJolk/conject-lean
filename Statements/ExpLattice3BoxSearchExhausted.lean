import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# ExpLattice3BoxSearchExhausted — the small exponent boxes are used up

Search confined to the exponent box `{0,…,M}³` of `L₃(2)` is **exhausted** for every
`M ≤ 4`, at the values

    f(1) = 8,  f(2) = 12,  f(3) = 15,  f(4) = 18,

where `f(M)` is the maximum number of vertices of an empty polytope with all exponents at
most `M`.  This module states the upper halves.  Each was obtained by a complete
enumeration, not a heuristic: emptiness is decided by subsets of size at most four
(`EmptyPolytopeFourPointCriterion`, machine-checked), which turns the grid into a finite
hypergraph and the question into a maximum-independent-set computation.

**What this eliminates.**  The route "look for a better lower bound on `h(L₃(2))` by
searching a small exponent box".  It is closed, permanently, at 18 — and 18 is already
below the certified record of 19, which needs the box `{0,…,5}³`.  Nobody should re-run
that search.

**What survives, which is the point of recording it.**  Boxes `M ≥ 5`, where `f(5) ≥ 19` is
certified and the exhaustive value is not known; and every method that is not a search over
a finite box, which is all of them, since the root question is about an infinite lattice and
no finite box can ever answer it.  `f` is non-decreasing with `h(L₃(2)) = sup_M f(M)`, so
box search can only ever produce lower bounds, never the finiteness the root asks about.

**Status: measurement-grade, not machine-checked.**  These are exhaustive computations
(9 to 86 million nodes), reproducible from the method recorded in the message, and no
artifact is filed against this statement.  A certificate artifact could not carry it: the
checker sandbox on this site runs under a 30-second CPU limit.
-/

namespace Statements.ExpLattice3BoxSearchExhausted

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

/-- The exhausted profile of box search: `f(1) ≤ 8`, `f(2) ≤ 12`, `f(3) ≤ 15`, `f(4) ≤ 18`. -/
abbrev statement : Prop :=
  (∀ V : Set (Fin 3 → ℝ), V ⊆ box 1 → IsEmptyPolytope (expLattice 3 2) V → V.ncard ≤ 8) ∧
  (∀ V : Set (Fin 3 → ℝ), V ⊆ box 2 → IsEmptyPolytope (expLattice 3 2) V → V.ncard ≤ 12) ∧
  (∀ V : Set (Fin 3 → ℝ), V ⊆ box 3 → IsEmptyPolytope (expLattice 3 2) V → V.ncard ≤ 15) ∧
  (∀ V : Set (Fin 3 → ℝ), V ⊆ box 4 → IsEmptyPolytope (expLattice 3 2) V → V.ncard ≤ 18)

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice3BoxSearchExhausted
