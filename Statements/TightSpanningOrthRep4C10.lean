import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# TightSpanningOrthRep4C10 — the k=4 seed, with tightness

Same witness as `SpanningOrthRep4C10`, plus the tightness condition that every three of the
ten vectors are linearly independent (no three in a common plane). Tightness is what makes
the seed reusable under relative-rotation amplification to sizes 10, 20, 30, ….

Convention: edge means orthogonal (opposite of Lovász–Saks–Schrijver). Graph: circulant
`C_10(1,2)`. Dimension 4; (k+1)-spanning means every five have rank 4.
-/

namespace Statements.TightSpanningOrthRep4C10

abbrev circDist (i j : Fin 10) : ℕ :=
  let d := (i.val + 10 - j.val) % 10
  min d (10 - d)

abbrev circEdge (i j : Fin 10) : Prop :=
  circDist i j = 1 ∨ circDist i j = 2

abbrev Rank4of5 (v : Fin 10 → Fin 4 → ℂ) (i j k l t : Fin 10) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

abbrev statement : Prop :=
  ∃ v : Fin 10 → Fin 4 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (circEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t → Rank4of5 v i j k l t) ∧
    (∀ i j k : Fin 10, i < j → j < k → LinearIndependent ℂ ![v i, v j, v k])

theorem target : statement := sorry

end Statements.TightSpanningOrthRep4C10
