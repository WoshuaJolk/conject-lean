import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# SpanningOrthRep5Clebsch — a 5-regular (6)-spanning orthogonal representation in C^5

Explicit integer witness: sixteen nonzero vectors in `ℤ^5 ⊂ ℂ^5` whose orthogonality graph
is exactly the Clebsch graph (the 5-regular strongly regular graph on 16 vertices obtained as
the Hamming graph on `(ℤ/2)^4` with edges at Hamming distance 1 or 4), with every six of the
sixteen spanning `ℂ^5`.

Convention: an edge means the two vectors *are* orthogonal (opposite of Lovász–Saks–Schrijver).
As with the icosahedral seed, (k+1)-spanning at k=5 is weaker than LSS general position; the
Clebsch graph is only 5-connected, so a general-position orth-rep in dimension 5 is ruled out
by Lovász–Saks–Schrijver, but a (6)-spanning one is not.
-/

namespace Statements.SpanningOrthRep5Clebsch

/-- Bit `k` of a vertex index in `Fin 16`. -/
abbrev bit (i : Fin 16) (k : Fin 4) : ℕ :=
  (i.val / (2 ^ k.val)) % 2

/-- Hamming distance on `(ℤ/2)^4`. -/
abbrev ham (i j : Fin 16) : ℕ :=
  (if bit i ⟨0, by omega⟩ ≠ bit j ⟨0, by omega⟩ then 1 else 0) +
  (if bit i ⟨1, by omega⟩ ≠ bit j ⟨1, by omega⟩ then 1 else 0) +
  (if bit i ⟨2, by omega⟩ ≠ bit j ⟨2, by omega⟩ then 1 else 0) +
  (if bit i ⟨3, by omega⟩ ≠ bit j ⟨3, by omega⟩ then 1 else 0)

/-- The Clebsch graph: edges at Hamming distance 1 or 4. -/
abbrev clebschEdge (i j : Fin 16) : Prop :=
  ham i j = 1 ∨ ham i j = 4

abbrev Rank5of6 (v : Fin 16 → Fin 5 → ℂ)
    (i1 i2 i3 i4 i5 i6 : Fin 16) : Prop :=
  LinearIndependent ℂ ![v i1, v i2, v i3, v i4, v i5] ∨
  LinearIndependent ℂ ![v i1, v i2, v i3, v i4, v i6] ∨
  LinearIndependent ℂ ![v i1, v i2, v i3, v i5, v i6] ∨
  LinearIndependent ℂ ![v i1, v i2, v i4, v i5, v i6] ∨
  LinearIndependent ℂ ![v i1, v i3, v i4, v i5, v i6] ∨
  LinearIndependent ℂ ![v i2, v i3, v i4, v i5, v i6]

abbrev statement : Prop :=
  ∃ v : Fin 16 → Fin 5 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (clebschEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i1 i2 i3 i4 i5 i6 : Fin 16,
      i1 < i2 → i2 < i3 → i3 < i4 → i4 < i5 → i5 < i6 →
        Rank5of6 v i1 i2 i3 i4 i5 i6)

theorem target : statement := sorry

end Statements.SpanningOrthRep5Clebsch
