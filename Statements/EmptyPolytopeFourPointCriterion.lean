import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# EmptyPolytopeFourPointCriterion

A finite set `V` of points of a set `S` in `ℝ³` is (the vertex set of) a convex polytope
empty in `S` **iff every subset of `V` with at most four elements is**.

This is what makes the whole problem finitely searchable.  Emptiness as ABFJN define it is a
global condition: it quantifies over the convex hull of `V`, and over all of `S`.  The
criterion below replaces it by a condition on subsets of size at most `4 = 3 + 1`, so
"empty" becomes an independence condition in a hypergraph whose edges are precomputable, and
an exhaustive search over empty subsets of a finite grid becomes a finite, complete
computation instead of a heuristic.

Both directions are needed and both are cheap.  Left to right is Carathéodory: a point of
`conv V` lies in the hull of an affinely independent subset, which in `ℝ³` has at most `4`
elements; if that subset is empty in `S` then the point is one of its own members.  Right to
left is heredity: every subset of an empty polytope is one, because a captured point would
have to be a non-vertex of the larger hull.

The bound `4` is `finrank ℝ (Fin 3 → ℝ) + 1`; the same statement holds in `ℝ^d` with `d + 1`.
-/

namespace Statements.EmptyPolytopeFourPointCriterion

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- Emptiness is decided by the subsets of size at most four. -/
abbrev statement : Prop :=
  ∀ (S V : Set (Fin 3 → ℝ)), V.Finite → V ⊆ S →
    ((∀ W, W ⊆ V → W.ncard ≤ 4 → IsEmptyPolytope S W) ↔ IsEmptyPolytope S V)

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.EmptyPolytopeFourPointCriterion
