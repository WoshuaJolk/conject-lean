import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB2334 — the root of p/14 at dimensions `(2,3,3,4)`

This is `MinUPBAtMostTrivialPlusOne` instantiated at a qubit, two qutrits and one
four-dimensional factor: an unextendible product basis of size at most `f_N + 1 = 10` in
`C^2 ⊗ C^3 ⊗ C^3 ⊗ C^4`, where `f_N = 1 + 1 + 2 + 2 + 3 = 9`.

The tuple is one of the smallest named open instances on the root statement. `f_N = 9` is odd
and two local dimensions are even, so Alon–Lovász's parity criterion gives `f_m ≥ 10`.
Chen–Johnston's Theorem 1 needs a dominating factor (`3 ≥ 5`, false), the system is neither
bipartite nor all-qubit, and no `(2,2,4k±1)`-type family applies. A witness of size 10 settles
the tuple optimally.

## Where the witness comes from

At size 10 exactly one factor is degenerate (`GenPosUPBTrivialCeiling`) and unextendibility is
a killing-number budget (`UPBFromDegreeBudget`). A degenerate qubit factor would force its
orthogonality class to be a disjoint union of 4-cycles, needing `4 | m`; `10 ≡ 2 (mod 4)`, so
the degenerate factor must be the quart, with the `C_10(1,2)` gadget of `SpanningOrthRep4C10`
(this board): killing number 4. The remaining distance classes of `Z_10` are all circulant and
carry the ordinary factors: the antipodal perfect matching (distance 5) is the qubit class
(killing number 1), the distance-3 class (a 10-cycle) and the distance-4 class (two 5-cycles)
are the two qutrit classes, realized in `C^3` with every three vectors linearly independent
(killing number 2 each). Budget `1 + 2 + 2 + 4 = 9 < 10`.

## Reading the formalisation

The proposition is the root's conclusion at `p = 4` and `d = (2,3,3,4)`, verbatim and in the
same order: the existential size `m`, the bound `m ≤ 2 + Σ_j (dims j − 1)`, nonzero local
vectors, pairwise orthogonality in some factor, and unextendibility against every product
vector with all local components nonzero, `∃ i` innermost.

`dims` is a plain comparison on the factor index rather than a list literal, so that
`Fin (dims j)` is reducible and the bound `2 + Σ_j (dims j − 1) = 10` is a `decide`-level fact.
-/

namespace Statements.MinUPB2334

/-- A qubit, two qutrits, and a four-dimensional factor. -/
abbrev dims : Fin 4 → ℕ := fun j => if j.val = 0 then 2 else if j.val < 3 then 3 else 4

abbrev statement : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
    ∃ v : Fin m → (j : Fin 4) → Fin (dims j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 4) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MinUPB2334
