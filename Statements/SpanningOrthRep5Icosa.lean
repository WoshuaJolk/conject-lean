import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# SpanningOrthRep5Icosa — a 5-regular (6)-spanning orthogonal representation in C^5

Explicit integer witness: twelve nonzero vectors in `ℤ^5 ⊂ ℂ^5` whose orthogonality graph
is exactly the icosahedral graph (the 1-skeleton of the regular icosahedron: 12 vertices,
5-regular, 30 edges), with every six of the twelve spanning `ℂ^5`.

Convention: an edge means the two vectors *are* orthogonal (opposite of Lovász–Saks–Schrijver).
The (k+1)-spanning predicate at k=5 asks that every six vectors have rank 5 (equivalently: some
five of them are linearly independent). This is strictly weaker than LSS general position
(every five independent), which is impossible for the icosahedral graph in dimension 5 because
that graph is only 5-connected and LSS requires (n−d)-connectivity (here 7).

The seed sits at m=12 > 2k=10, above the Chen–Johnston gadget-size ceiling that applies to
certain published constructions.
-/

namespace Statements.SpanningOrthRep5Icosa

/-- Northern / southern poles and two pentagons: the standard icosahedral adjacency on `Fin 12`. -/
abbrev icosaEdge (i j : Fin 12) : Prop :=
  let a := min i.val j.val
  let b := max i.val j.val
  (a = 0 ∧ 1 ≤ b ∧ b ≤ 5) ∨
  (b = 11 ∧ 6 ≤ a ∧ a ≤ 10) ∨
  (1 ≤ a ∧ a ≤ 5 ∧ 1 ≤ b ∧ b ≤ 5 ∧ (b = a + 1 ∨ (a = 1 ∧ b = 5))) ∨
  (6 ≤ a ∧ a ≤ 10 ∧ 6 ≤ b ∧ b ≤ 10 ∧ (b = a + 1 ∨ (a = 6 ∧ b = 10))) ∨
  (1 ≤ a ∧ a ≤ 5 ∧ 6 ≤ b ∧ b ≤ 10 ∧
    (b = a + 5 ∨ b = 6 + (a + 3) % 5))

/-- Six vectors in `ℂ^5` span the ambient space iff some five of them are linearly independent. -/
abbrev Rank5of6 (v : Fin 12 → Fin 5 → ℂ)
    (i1 i2 i3 i4 i5 i6 : Fin 12) : Prop :=
  LinearIndependent ℂ ![v i1, v i2, v i3, v i4, v i5] ∨
  LinearIndependent ℂ ![v i1, v i2, v i3, v i4, v i6] ∨
  LinearIndependent ℂ ![v i1, v i2, v i3, v i5, v i6] ∨
  LinearIndependent ℂ ![v i1, v i2, v i4, v i5, v i6] ∨
  LinearIndependent ℂ ![v i1, v i3, v i4, v i5, v i6] ∨
  LinearIndependent ℂ ![v i2, v i3, v i4, v i5, v i6]

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∃ v : Fin 12 → Fin 5 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (icosaEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i1 i2 i3 i4 i5 i6 : Fin 12,
      i1 < i2 → i2 < i3 → i3 < i4 → i4 < i5 → i5 < i6 →
        Rank5of6 v i1 i2 i3 i4 i5 i6)

theorem target : statement := sorry

end Statements.SpanningOrthRep5Icosa
