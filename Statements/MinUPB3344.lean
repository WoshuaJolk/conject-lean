import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB3344 — the root of p/14 at dimensions `(3,3,4,4)`

This is `MinUPBAtMostTrivialPlusOne` instantiated at two qutrits and two four-dimensional
factors: an unextendible product basis of size at most `f_N + 1 = 12` in
`C^3 ⊗ C^3 ⊗ C^4 ⊗ C^4`, where `f_N = 1 + 2 + 2 + 3 + 3 = 11`.

The tuple sits in the exceptional regime (`f_N` odd, two even dimensions) with no qubit factor,
so no published family reaches it: Alon–Lovász's parity criterion gives `f_m ≥ 12`,
Chen–Johnston's Theorem 1 needs a dominating factor (`3 ≥ 7`, false), and the system is neither
bipartite nor all-qubit. A witness of size 12 settles it optimally.

## Where the witness comes from

At size 12 exactly one factor is degenerate (`GenPosUPBTrivialCeiling`) and unextendibility is
a killing-number budget (`UPBFromDegreeBudget`). The degenerate factor must be a quart (a
degenerate qutrit would need killing number 3 with a 3-regular orthogonality graph — but the
budget then forces the shape elsewhere; the all-circulant decomposition below uses the quart),
with killing number 4: the squared cycle `C_12(1,2)` realized over the Gaussian integers — the
same gadget as `MinUPB445`, and the reason one `k = 4` object settles both m = 12 tuples.

The ordinary classes are the remaining distance classes of `Z_12`: the distance-4 class (four
disjoint triangles) and the distance-5 class (a 12-cycle) carry the two qutrits, each realized
by integer vectors with every three linearly independent (killing number 2); the class
`C_12(3,6)`, three disjoint `K_4`'s, carries the ordinary quart via three integer orthogonal
frames in general position (killing number 3). Budget `2 + 2 + 4 + 3 = 11 < 12`.

## Reading the formalisation

The proposition is the root's conclusion at `p = 4` and `d = (3,3,4,4)`, verbatim and in the
same order: the existential size `m`, the bound `m ≤ 2 + Σ_j (dims j − 1)`, nonzero local
vectors, pairwise orthogonality in some factor, and unextendibility against every product
vector with all local components nonzero, `∃ i` innermost.

`dims` is a plain comparison on the factor index rather than a list literal, so that
`Fin (dims j)` is reducible and the bound `2 + Σ_j (dims j − 1) = 12` is a `decide`-level fact.
-/

namespace Statements.MinUPB3344

/-- Two qutrits and two four-dimensional factors. -/
abbrev dims : Fin 4 → ℕ := fun j => if j.val < 2 then 3 else 4

abbrev statement : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
    ∃ v : Fin m → (j : Fin 4) → Fin (dims j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 4) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MinUPB3344
