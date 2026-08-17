import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB224kMinus1 — Chen–Johnston open case (1), the general-`k` question

Chen & Johnston, *Minimal and maximal unextendible product bases*, Commun. Math. Phys. **333**
(2015) 351–365 (= arXiv:1301.1406v1), §6 "Outlook", list as open case (1):

> `d₁ = d₂ = 2, d₃ = 4k−1`: It was shown in [Fen06] that `fm(2,2,4k−1) = fN(2,2,4k−1)+1`
> when `k = 1`, but the proof technique does not seem to generalize straightforwardly to
> the `k ≥ 2` case.

Here `f_m(d₁,…,d_p)` is the minimum cardinality of an unextendible product basis of
`C^{d₁} ⊗ ⋯ ⊗ C^{d_p}`, and `f_N(2,2,4k−1) = 1 + (2−1) + (2−1) + (4k−1−1) = 4k+1`, so the
conjectured value is `4k+2`.

The matching **lower** bound `f_m(2,2,4k−1) ≥ 4k+2` is already a published theorem, for every
`k ≥ 1`: Alon & Lovász, *Unextendible product bases*, J. Combin. Theory Ser. A **95** (2001)
169–179, Corollary 4.1(i) — if some `kᵢ` is even and `n = 1 + Σ(kᵢ−1)` is odd then
`f_m(k₁,…,k_m) > n`; here `n = 4k+1` is odd and `k₁ = 2` is even.

So the entire open content of case (1) is the **existence** half, and that is what this
statement says: for every `k ≥ 2` there are `4k+2` product states in `C² ⊗ C² ⊗ C^{4k−1}`
that are pairwise orthogonal and admit no orthogonal product state. Conditional on the cited
Alon–Lovász corollary, this statement is equivalent to `f_m(2,2,4k−1) = 4k+2` for all `k ≥ 2`.

## Reading the formalisation

A product state `|u⟩⊗|w⟩⊗|z⟩` is recorded by its three factors; no tensor product is formed.
The inner product is the standard Hermitian one, conjugate-linear in the first slot, so
`⟨ψᵢ|ψⱼ⟩ = ⟨uᵢ|uⱼ⟩⟨wᵢ|wⱼ⟩⟨zᵢ|zⱼ⟩` is the displayed triple product. (The convention is not
load-bearing: both orthogonality and non-orthogonality are invariant under conjugating the
whole expression.)

* clause 1–3: every factor is nonzero, so every `|ψᵢ⟩` is a nonzero product state;
* clause 4: the `4k+2` states are pairwise orthogonal;
* clause 5: **unextendibility** — for every nonzero product vector `|a⟩⊗|b⟩⊗|c⟩` there is
  some `i` with `⟨ψᵢ|a⊗b⊗c⟩ ≠ 0`. Equivalently the orthocomplement of the span contains no
  nonzero product vector.

The usual extra requirement that a UPB span a *proper* subspace is automatic at these
parameters and is therefore not restated: pairwise-orthogonal nonzero vectors are linearly
independent, so the span has dimension exactly `4k+2`, and `4k+2 < 4(4k−1) = dim` for every
`k ≥ 2`. That arithmetic fact is filed separately as `UPBProperSpan224k`.

## What is known at pose time

`k = 1` (`d₃ = 3`) is Feng, Discrete Appl. Math. **154** (2006) 942–949, and is outside the
scope of this statement. For `k = 2, 3, 4` there are explicit exact computational certificates
— `f_m(2,2,7) = 10`, `f_m(2,2,11) = 14`, `f_m(2,2,15) = 18` — from a prior campaign
(`jig.so/reports/41`, independently re-checked in `jig.so/reports/41b`), but none of them is
machine-verified against this statement yet. Every `k ≥ 5` is untouched.

## How to attack a single case

Unextendibility is a finite check, but the naive form is `3^n` rank computations — one per
assignment of the `n` indices to the three parties — which is `3^10 = 59049` already at
`k = 2` and `3^22 ≈ 3.1·10^10` at `k = 5`. That does not fit in a kernel. Use instead:

* For nonzero `a : C²` the states it annihilates are exactly those whose `uᵢ` lies on a single
  line, so the `u`-directions partition the index set into parallel classes and `a` kills one
  class or none; likewise `b` for the `w`-directions. So it suffices to check, for each pair
  `(A,B)` of a `u`-class (or `∅`) and a `w`-class (or `∅`), that `{zᵢ : i ∉ A ∪ B}` spans
  `C^(4k−1)`. Spanning is monotone in the index set, so only the maximal removals matter.
* Since `4k+2 = (4k−1) + 3`, every such `A ∪ B` must have at most `3` elements. Hence every
  parallel class has size at most `2`, and the construction has no slack anywhere.
* Certify each spanning condition rather than searching for it: give `4k−1` surviving indices
  `T`, an integer matrix `N`, and a nonzero integer `m` with `Z_T · N = m · I`, where `Z_T` has
  the `zᵢ, i ∈ T` as rows. Ranks of a rational matrix agree over `ℚ`, `ℝ` and `ℂ`, so an
  integer-entry witness may be certified entirely over `ℚ`.

## Known barriers

* Chen–Johnston's own Theorem 1 needs `d_p − 1 ≥ Σ_{j<p}(d_j − 1) ≥ 3`; for `(2,2,d)` that sum
  is `2`, so the whole family sits exactly one below their threshold, and their Theorem 3
  recovers only `d₃ ≡ 1 (mod 4)`.
* The Alon–Lovász route through orthogonal representations (their Theorem 3.1: `f_m = n` iff
  `K_n` admits an `(n−k₁,…,n−k_m)`-connected edge colouring) is an *iff only in the tight case*
  `f_m = n`. Here `f_m = n+1`, so that equivalence does not apply.
* Lovász–Saks–Schrijver give no efficient deterministic construction of a general-position
  orthogonal representation, so the genericity route yields existence, not vectors.
-/

namespace Statements.MinUPB224kMinus1

/-- The canonical proposition. This is the type the verifier demands.

For every integer `k ≥ 2` there exist `4k+2` nonzero product states
`|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩ ∈ C² ⊗ C² ⊗ C^(4k−1)` which are pairwise orthogonal and which no
nonzero product state is orthogonal to. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ u : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∃ w : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∃ z : Fin (4 * k + 2) → Fin (4 * k - 1) → ℂ,
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
        ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0)

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPB224kMinus1
