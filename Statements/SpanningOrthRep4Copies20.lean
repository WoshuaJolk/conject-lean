import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Matrix.Basic

/-!
# SpanningOrthRep4Copies20 — a 4-regular 5-spanning orthogonal representation in C^4 on 20 vertices

Convention (as in `SpanningOrthRep4C10`, the opposite of Lovász–Saks–Schrijver): an edge of the
orthogonality graph means the two vectors *are* orthogonal.

At the target size `f_N + 1` the degree budget (`GenPosUPBTrivialCeiling`, `UPBFromDegreeBudget`)
forces exactly one factor of the witness to be degenerate: its orthogonality graph is `k`-regular
in dimension `k`, while no `k + 1` of its local vectors lie in a common hyperplane
(`(k+1)`-spanning). Chen–Johnston construct such a representation for every `k`, but only on at
most `2k` vertices, and that ceiling is precisely their dominance hypothesis — so the reach of
their theorem is the reach of the gadget.

This statement breaks the ceiling at `k = 4`: it asks for `20` vertices where `2k = 8`. The graph
is two disjoint copies of the circulant `C_10(1,2)`, i.e. two copies of the `k = 4` seed of
`SpanningOrthRep4C10` (jig.so/p/14?s=6), which is the shape produced by placing several copies of
a seed in generic relative position. Beyond the `(k+1)`-spanning conclusion the statement also
demands *tightness* — every three of the twenty vectors are independent — because tightness is the
hypothesis under which a seed can be re-copied, so a tight witness is reusable rather than
isolated.

The `k = 3` analogue is the Petersen representation of jig.so/p/13 (10 vertices, ceiling 6), and
`k = 2` is the repeated-vector trick of jig.so/p/6. No claim is made here about other graphs,
other dimensions, other sizes, or any general connectivity criterion.
-/

namespace Statements.SpanningOrthRep4Copies20

/-- Circular distance on `Fin 10`. -/
abbrev circDist (i j : Fin 10) : ℕ :=
  let d := (i.val + 10 - j.val) % 10
  min d (10 - d)

/-- The block of a vertex of `Fin 20`: two blocks of ten. -/
abbrev blk (i : Fin 20) : ℕ := i.val / 10

/-- The position of a vertex inside its block. -/
abbrev posn (i : Fin 20) : ℕ := i.val % 10

/-- Two disjoint copies of the circulant `C_10(1,2)`: an edge joins two vertices of the same
block whose positions are at circular distance `1` or `2`. -/
abbrev twoCircEdge (i j : Fin 20) : Prop :=
  blk i = blk j ∧
    (circDist ⟨posn i, Nat.mod_lt _ (by norm_num)⟩ ⟨posn j, Nat.mod_lt _ (by norm_num)⟩ = 1 ∨
     circDist ⟨posn i, Nat.mod_lt _ (by norm_num)⟩ ⟨posn j, Nat.mod_lt _ (by norm_num)⟩ = 2)

/-- Five vectors span `C^4` iff some four of them are linearly independent. -/
abbrev Rank4of5 (v : Fin 20 → Fin 4 → ℂ) (i j k l t : Fin 20) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

/-- The canonical proposition.

There exist twenty nonzero vectors in `C^4` whose orthogonality graph is exactly two disjoint
copies of the circulant `C_10(1,2)` (edge iff the Hermitian pairing vanishes), of which every
three are linearly independent, and of which no five lie in a common hyperplane. -/
abbrev statement : Prop :=
  ∃ v : Fin 20 → Fin 4 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (twoCircEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i j k : Fin 20, i < j → j < k → LinearIndependent ℂ ![v i, v j, v k]) ∧
    (∀ i j k l t : Fin 20, i < j → j < k → k < l → l < t → Rank4of5 v i j k l t)

theorem target : statement := sorry

end Statements.SpanningOrthRep4Copies20
