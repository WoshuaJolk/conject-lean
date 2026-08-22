import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB2244 — the root of p/14 at dimensions `(2,2,4,4)`

This is `MinUPBAtMostTrivialPlusOne` instantiated at two qubits and two four-dimensional
factors: an unextendible product basis of size at most `f_N + 1 = 10` in
`C^2 ⊗ C^2 ⊗ C^4 ⊗ C^4`, where `f_N = 1 + 1 + 1 + 3 + 3 = 9`.

The tuple is one of the smallest named open instances on the root statement. `f_N = 9` is odd
and not every local dimension is odd, so Alon–Lovász's parity criterion gives
`f_m ≥ f_N + 1 = 10`. Chen–Johnston's Theorem 1 needs a dominating factor
(`d_p − 1 ≥ Σ_{j<p}(d_j − 1)`, here `3 ≥ 5`, false), the system is neither bipartite nor
all-qubit, and `(2,2,4,4)` matches neither `(2,2,4k±1)` family. So a witness of size 10
settles a case no published result reaches, and by the parity lower bound settles it optimally.

## Where the witness comes from

The two green engines fix the shape: `GenPosUPBTrivialCeiling` forces exactly one degenerate
factor at size 10, and `UPBFromDegreeBudget` reduces unextendibility to a killing-number budget
`Σ c_j < 10`. The orthogonality graphs must partition `E(K_10)` with degrees summing to 9.

A qubit cannot be the degenerate factor here: an exactly-2-regular orthogonality class in `C^2`
is forced to be a disjoint union of 4-cycles (each vertex's two neighbours share its orthogonal
line, so components are cycles with lines alternating `ℓ, ℓ^⊥`; odd cycles are impossible and
even cycles of length ≥ 6 create chords), which needs `4 | m`, and `10 ≡ 2 (mod 4)`. So the
degenerate factor must be a quart, with killing number 4: ten vectors in `C^4`, 4-regular
orthogonality graph, no five in a common hyperplane. That gadget is `SpanningOrthRep4C10`
(this board): the circulant `C_10(1,2)` on the distance-1 and distance-2 edges of `Z_10`.

The remaining distance classes of `Z_10` supply the ordinary factors: the distance-3 class is a
10-cycle whose two perfect matchings become the two qubit classes (killing number 1 each), and
the distance-4 and distance-5 classes together form the pentagonal prism `C_10(4,5)`, realized
in `C^4` in general position (killing number 3). Budget `1 + 1 + 3 + 4 = 9 < 10`.

## Reading the formalisation

The proposition is the root's conclusion at `p = 4` and `d = (2,2,4,4)`, verbatim and in the
same order: the existential size `m`, the bound `m ≤ 2 + Σ_j (dims j − 1)`, nonzero local
vectors, pairwise orthogonality in some factor, and unextendibility against every product
vector with all local components nonzero, `∃ i` innermost.

`dims` is a plain comparison on the factor index rather than a list literal, so that
`Fin (dims j)` is reducible and the bound `2 + Σ_j (dims j − 1) = 10` is a `decide`-level fact.
-/

namespace Statements.MinUPB2244

/-- Two qubits and two four-dimensional factors. -/
abbrev dims : Fin 4 → ℕ := fun j => if j.val < 2 then 2 else 4

abbrev statement : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
    ∃ v : Fin m → (j : Fin 4) → Fin (dims j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 4) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MinUPB2244
