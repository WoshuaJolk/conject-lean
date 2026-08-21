import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB344 — Chen–Johnston open case (3), the single finite instance

Chen & Johnston, *The minimum size of unextendible product bases in the bipartite
case (and some multipartite cases)*, Commun. Math. Phys. **333** (2015) 351–365
(= arXiv:1301.1406v1), §6 "Outlook", list as open case (3):

> `d₁ = 3, d₂ = d₃ = 4`: Excluding the open case (1) above, this is now the
> smallest unsolved tripartite case.

Here `f_m(d₁,…,d_p)` is the minimum cardinality of an unextendible product basis of
`C^{d₁} ⊗ ⋯ ⊗ C^{d_p}`, and the trivial lower bound is
`f_N(3,4,4) = 1 + (3−1) + (4−1) + (4−1) = 9`.

The matching **lower** bound `f_m(3,4,4) ≥ 10` is already a published theorem:
Alon & Lovász, *Unextendible product bases*, J. Combin. Theory Ser. A **95** (2001)
169–179, Corollary 4.1(i) — if some `kᵢ` is even and `n = 1 + Σ(kᵢ−1)` is odd then
`f_m(k₁,…,k_m) > n`; here `n = 9` is odd and `k₂ = 4` is even.

So the entire open content of case (3) is the **existence** half at cardinality 10,
and that is what this statement says: there are `10` product states in
`C³ ⊗ C⁴ ⊗ C⁴` that are pairwise orthogonal and admit no orthogonal product state.
Conditional on the cited Alon–Lovász corollary, this statement is equivalent to
`f_m(3,4,4) = 10`.

## Reading the formalisation

A product state `|u⟩⊗|w⟩⊗|z⟩` is recorded by its three factors; no tensor product is
formed. The inner product is the standard Hermitian one, conjugate-linear in the
first slot, so `⟨ψᵢ|ψⱼ⟩ = ⟨uᵢ|uⱼ⟩⟨wᵢ|wⱼ⟩⟨zᵢ|zⱼ⟩` is the displayed triple product.

* clause 1–3: every factor is nonzero, so every `|ψᵢ⟩` is a nonzero product state;
* clause 4: the `10` states are pairwise orthogonal;
* clause 5: **unextendibility** — for every nonzero product vector `|a⟩⊗|b⟩⊗|c⟩`
  there is some `i` with `⟨ψᵢ|a⊗b⊗c⟩ ≠ 0`.

The usual extra requirement that a UPB span a *proper* subspace is automatic:
`10 < 3·4·4 = 48`. That arithmetic is filed separately as `UPBProperSpan344`.

## What is known at pose time

* Lower bound `10`: Alon–Lovász Cor. 4.1(i), as above.
* Upper bound `40`: Shi, Li, Chen & Zhang, *Strong quantum nonlocality for
  unextendible product bases in heterogeneous systems*, J. Phys. A **55** (2022)
  015305 (= arXiv:2201.00085), Proposition 4 — for `3 ≤ d_A ≤ d_B ≤ d_C` there is a
  UPB of size `d_A d_B d_C − 8`; at `(3,4,4)` that is `48 − 8 = 40`.
* Chen–Johnston Theorem 1 does not apply: it needs `d_p − 1 ≥ Σ_{j<p}(d_j − 1)`,
  but here `3 ≱ 2+3 = 5`.
* Case (1) of the same Outlook (`(2,2,4k−1)`) is a separate problem on this board
  (`MinUPB224kMinus1`) and is out of scope. Case (2) (qubit systems with `4k`
  parties) was settled by Johnston, TQC 2013, and is out of scope.
-/

namespace Statements.MinUPB344

/-- The canonical proposition. This is the type the verifier demands.

There exist `10` nonzero product states
`|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩ ∈ C³ ⊗ C⁴ ⊗ C⁴` which are pairwise orthogonal and which no
nonzero product state is orthogonal to. -/
abbrev statement : Prop :=
  ∃ u : Fin 10 → Fin 3 → ℂ,
  ∃ w : Fin 10 → Fin 4 → ℂ,
  ∃ z : Fin 10 → Fin 4 → ℂ,
    (∀ i, u i ≠ 0) ∧
    (∀ i, w i ≠ 0) ∧
    (∀ i, z i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∑ r, star (u i r) * u j r) *
      (∑ r, star (w i r) * w j r) *
      (∑ r, star (z i r) * z j r) = 0) ∧
    (∀ a : Fin 3 → ℂ, a ≠ 0 → ∀ b : Fin 4 → ℂ, b ≠ 0 →
      ∀ c : Fin 4 → ℂ, c ≠ 0 →
      ∃ i,
        (∑ r, star (u i r) * a r) *
        (∑ r, star (w i r) * b r) *
        (∑ r, star (z i r) * c r) ≠ 0)

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPB344
