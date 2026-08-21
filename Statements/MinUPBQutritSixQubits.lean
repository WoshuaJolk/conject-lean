import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPBQutritSixQubits — the root of p/14 at dimensions `(3,2,2,2,2,2,2)`

This is `MinUPBAtMostTrivialPlusOne` instantiated at one qutrit and six qubits: it asserts the
existence of an unextendible product basis of size at most `f_N + 1 = 10` in
`C^3 ⊗ (C^2)^{⊗6}`, where `f_N = 1 + 2 + 6·1 = 9`.

The tuple is open in the literature. Alon–Lovász gives `f_m ≥ f_N + 1` here, since `f_N = 9` is
odd and not every local dimension is odd. Chen–Johnston's Theorem 1 needs one factor to dominate
(`d_p − 1 ≥ Σ_{j<p} (d_j − 1)`, here `2 ≥ 7`, false), so it says nothing; the system is neither
bipartite nor all-qubit, so neither Corollary 2 nor Feng's `p ≡ 2 (mod 4)` result applies; and
`(3,2^6)` is not among the finitely many tuples listed as known in Chen–Johnston §2. So a
witness of size 10 settles a case that no published result reaches, and settles it optimally.

## Where the witness comes from

`GenPosUPBTrivialCeiling` (`jig.so/p/14?s=2`) forces every size-`(f_N + 1)` witness to spend
exactly one unit of local degeneracy, and `UPBFromDegreeBudget` turns unextendibility into the
inequality `Σ_j c_j < m` for per-factor killing numbers `c_j`. Here the budget is
`3 + 6·1 = 9 < 10`: the qutrit factor is the degenerate one, with killing number `3 = d` rather
than `2 = d − 1`, and each qubit factor is in general position with killing number `1`.

That fixes the combinatorics completely. The qutrit factor's orthogonality graph is 3-regular on
10 vertices and the six qubit factors' graphs are perfect matchings, so the seven graphs
partition the 45 edges of `K_10`, which happens precisely when the 3-regular graph's complement
is 1-factorizable. Taking the Petersen graph works: `K_10` is the edge-disjoint union of the
Petersen graph and six perfect matchings.

The vectors are then explicit and integral. The qutrit factor reuses, verbatim, the `C^3` local
family of the size-10 UPB in `C^3 ⊗ C^4 ⊗ C^4` from `MinUPB344` (`jig.so/p/13`) — the same ten
integer vectors realizing Petersen orthogonality with no four of them coplanar, which is exactly
killing number 3. Each qubit factor assigns the five pairs of its matching the five direction
pairs `{(1,t), (−t,1)}` for `t = 1,…,5`; those ten directions are pairwise non-parallel, giving
killing number 1, and `(1,t)·(−s,1) = t − s` vanishes only within a pair.

## Reading the formalisation

The proposition is the root's conclusion at `p = 7` and `d = (3,2,2,2,2,2,2)`, verbatim and in
the same order, so a proof of this is literally a case of `MinUPBAtMostTrivialPlusOne`: the
existential size `m`, the bound `m ≤ 2 + Σ_j (d j − 1)`, nonzero local vectors, pairwise
orthogonality in some factor, and unextendibility against every product vector with all factors
nonzero, `∃ i` innermost.

`dims` is a plain `if` on the factor index rather than a list literal, so that `Fin (dims j)` is
reducible and the bound `2 + Σ_j (dims j − 1) = 10` is a `decide`-level fact.
-/

namespace Statements.MinUPBQutritSixQubits

/-- One qutrit and six qubits. -/
abbrev dims : Fin 7 → ℕ := fun j => if j = 0 then 3 else 2

abbrev statement : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
    ∃ v : Fin m → (j : Fin 7) → Fin (dims j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 7) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MinUPBQutritSixQubits
