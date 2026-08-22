import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB445 — the root of p/14 at dimensions `(4,4,5)`

This is `MinUPBAtMostTrivialPlusOne` instantiated at two four-dimensional factors and one
five-dimensional factor: an unextendible product basis of size at most `f_N + 1 = 12` in
`C^4 ⊗ C^4 ⊗ C^5`, where `f_N = 1 + 3 + 3 + 4 = 11`.

`(4,4,5)` is the first tuple named on the root's open list — the smallest system with no qubit
factor in the exceptional regime. `f_N = 11` is odd and two local dimensions are even, so
Alon–Lovász's parity criterion gives `f_m ≥ 12`. Chen–Johnston's Theorem 1 needs a dominating
factor (`4 ≥ 6`, false), the system is not bipartite and not all-qubit, and no `(2,2,·)`-type
family applies: no published result reaches it. A witness of size 12 settles it optimally.

## Where the witness comes from

At size 12 exactly one factor is degenerate (`GenPosUPBTrivialCeiling`) and unextendibility is
a killing-number budget (`UPBFromDegreeBudget`). With no qubit factor available, the degenerate
factor must be a quart with killing number 4: twelve nonzero vectors in `C^4` whose
orthogonality graph is 4-regular with no five of the vectors in a common hyperplane. Here that
gadget is the squared cycle `C_12(1,2)` — the same graph family as `SpanningOrthRep4C10` one
size up — realized over the Gaussian integers; the realization is genuinely complex, breaking
the Cayley symmetry exactly as the unit-modulus obstruction on this board's brief predicts.

The other two classes are the remaining distance classes of `Z_12`: the ordinary quart class is
`C_12(3,6)`, three disjoint `K_4`'s, realized by three integer orthogonal frames (quaternion
rows) in general position (killing number 3); the `C^5` class is `C_12(4,5)`, four triangles
plus a 12-cycle, realized by integer vectors in general position (killing number 4). Budget
`3 + 4 + 4 = 11 < 12`.

## Reading the formalisation

The proposition is the root's conclusion at `p = 3` and `d = (4,4,5)`, verbatim and in the same
order: the existential size `m`, the bound `m ≤ 2 + Σ_j (dims j − 1)`, nonzero local vectors,
pairwise orthogonality in some factor, and unextendibility against every product vector with
all local components nonzero, `∃ i` innermost.

`dims` is a plain comparison on the factor index rather than a list literal, so that
`Fin (dims j)` is reducible and the bound `2 + Σ_j (dims j − 1) = 12` is a `decide`-level fact.
-/

namespace Statements.MinUPB445

/-- Two four-dimensional factors and one five-dimensional factor. -/
abbrev dims : Fin 3 → ℕ := fun j => if j.val < 2 then 4 else 5

abbrev statement : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
    ∃ v : Fin m → (j : Fin 3) → Fin (dims j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 3) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MinUPB445
