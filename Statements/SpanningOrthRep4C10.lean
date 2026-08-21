import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Matrix.Basic

/-!
# SpanningOrthRep4C10 — a 4-regular (5)-spanning orthogonal representation in C^4

Lovász–Saks–Schrijver characterise graphs with a *general-position* orthogonal representation
in R^d: every d of the vectors are linearly independent. The present statement weakens that
non-degeneracy by exactly one unit — every 5 of the vectors span C^4, but some 4 may be
dependent — and asks only for existence of one concrete 4-regular example.

Convention warning: here an edge means the two vectors *are* orthogonal (the opposite of the
LSS convention, where nonadjacent vertices get orthogonal vectors). Under this convention the
graph is the circulant C_10(1,2): vertices Z/10Z, edges between vertices at circular distance
1 or 2, which is 4-regular on 10 vertices.

This is the k=4 datum requested for the degenerate-orthogonal-representation lemma that the
root of this problem reduces to (see the problem brief). The k=3 case is the Petersen witness
on jig.so/p/13; k=2 is the repetition trick. The monomial-curve route to such representations
is already ruled out in the brief and is not used here.
-/

namespace Statements.SpanningOrthRep4C10

/-- Circular distance on `Fin 10`. -/
abbrev circDist (i j : Fin 10) : ℕ :=
  let d := (i.val + 10 - j.val) % 10
  min d (10 - d)

/-- The circulant graph `C_10(1,2)`. -/
abbrev circEdge (i j : Fin 10) : Prop :=
  circDist i j = 1 ∨ circDist i j = 2

/-- Five vectors in `C^4` span the ambient space iff some four of them are linearly independent. -/
abbrev Rank4of5 (v : Fin 10 → Fin 4 → ℂ) (i j k l t : Fin 10) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

/-- The canonical proposition.

There exist ten nonzero vectors in `C^4` whose orthogonality graph is exactly the circulant
`C_10(1,2)` (edge iff Hermitian inner product vanishes) and of which no five lie in a common
hyperplane. -/
abbrev statement : Prop :=
  ∃ v : Fin 10 → Fin 4 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (circEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t → Rank4of5 v i j k l t)

theorem target : statement := sorry

end Statements.SpanningOrthRep4C10
