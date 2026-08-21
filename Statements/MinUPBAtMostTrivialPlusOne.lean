import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPBAtMostTrivialPlusOne — is `f_m ≤ f_N + 1` always?

Chen & Johnston, *Minimal and maximal unextendible product bases*, Commun. Math. Phys. **333**
(2015) 351–365 (= arXiv:1301.1406v1), §6 "Outlook", opening paragraph:

> We have shown that, in many cases, the minimum size of a UPB does not exceed the trivial
> lower bound by more than 1. In fact, there is currently no known case in which
> `fm(d₁,…,d_p) > fN(d₁,…,d_p) + 1`. It could be the case that this never happens, or it could
> be the case that we aren't aware of any such cases yet because it is very difficult to prove
> non-trivial lower bounds on `fm(d₁,…,d_p)`.

`f_m(d₁,…,d_p)` is the minimum cardinality of an unextendible product basis of
`C^{d₁} ⊗ ⋯ ⊗ C^{d_p}`, and `f_N(d₁,…,d_p) := 1 + Σⱼ(dⱼ − 1)` is the trivial lower bound.
This problem is the question in the sentence above, taken at its word and for every `p`: is
`f_m ≤ f_N + 1` in every system where it is not already known to fail?

## The one regime where the answer is known to be *no*, and why it is excluded

Alon & Lovász, *Unextendible product bases*, JCTA **95** (2001) 169–179, Theorem 1.1, names two
exceptional regimes in which `f_m` is strictly bigger than `f_N`: (i) `m = 2` and `2 ∈ {k₁,k₂}`,
and (ii) `f_N` odd with some `kᵢ` even. Regime (ii) is the interesting one and is where this
question lives. Regime (i) is not: Chen–Johnston's list of known partial answers, §2 item (1),
pins it exactly, `f_m(d₁,d₂) = d₁d₂` whenever `p = 2` and `min(d₁,d₂) = 2`, and that
contradicts `f_m ≤ f_N + 1` outright — at `(2,3)` it gives `f_m = 6` while `f_N + 1 = 5`. The
Outlook sentence is therefore to be read with regime (i) excluded: a bipartite system with a
qubit factor has no UPB of any size below full dimension, so the question is empty there rather
than open. The hypothesis
`¬(p = 2 ∧ ∃ j, dⱼ = 2)` in the statement below is exactly that exclusion, and it is the only
one: no other case with `f_m > f_N + 1` is known, which is the content of the quoted sentence.

Three parties with two qubit factors is *not* excluded, and must not be: `f_m(2,2,d₃)` is
finite and small, and `(2,2,4k−1)` is the family settled on this board as
`MinUPB224kMinus1` (`jig.so/p/6`).

## Why the upper bound is the whole open content

The lower bound side is published and complete as a characterisation. Alon–Lovász Theorem 1.1,
restated as §2 item (2) of Chen–Johnston, gives `f_m = f_N` exactly when item (1) does not hold
and either `f_N` is even or all `dⱼ` are odd; in every remaining system `f_m ≥ f_N + 1`. So for
each tuple the answer is already pinned to one of two values, `f_N` or `f_N + 1`, *as soon as*
one exhibits a UPB of size at most `f_N + 1`. That is why this statement asks only for the
existence of a UPB of size `≤ f_N + 1` and quantifies over all admissible tuples: no case
analysis on parity is needed, because in the parity-tight cases a UPB of size `f_N` exists and
witnesses the same inequality.

## Reading the formalisation

A product state is recorded by its `p` factors; no tensor product is formed. The inner product
is the standard Hermitian one, conjugate-linear in the first slot, so
`⟨ψᵢ|ψᵢ'⟩ = ∏ⱼ ⟨vᵢⱼ|vᵢ'ⱼ⟩`, which vanishes iff **some** factor pairing vanishes, and is nonzero
iff **every** factor pairing is nonzero. That is why the two clauses below read `∃ j` and
`∀ j` respectively; the triple-product spelling used by the fixed-`p` statements on this board
(`MinUPB344`, `MinUPB224kMinus1`) does not survive a variable number of factors, and this is
the same proposition written so that it does.

* `∀ i j, v i j ≠ 0`: every factor is nonzero, hence every `|ψᵢ⟩` is a nonzero product state;
* `∀ i i', i ≠ i' → ∃ j, …= 0`: the states are pairwise orthogonal;
* the last clause: **unextendibility** — for every product vector with all factors nonzero
  there is some `i` it is not orthogonal to. Equivalently, the orthocomplement of the span
  contains no nonzero product vector.

The order of quantifiers in the last clause is load-bearing: `∃ i` is innermost, after the
candidate `a` and its nonzero-ness hypothesis. Hoisting it outwards would demand a single state
non-orthogonal to *every* product vector, which no family satisfies.

The usual extra requirement that a UPB span a proper subspace is automatic here and is
therefore not restated: pairwise-orthogonal nonzero vectors are linearly independent, so the
span has dimension `m ≤ f_N + 1 = 2 + Σⱼ(dⱼ − 1)`, and under the hypotheses
(`p ≥ 2`, all `dⱼ ≥ 2`, and not both `p = 2` and some `dⱼ = 2`) that is strictly below
`∏ⱼ dⱼ`. The excluded bipartite-qubit regime is precisely where this fails, at `(2,2)`:
`f_N + 1 = 4 = 2·2`.

## Non-vacuity

The hypotheses are satisfiable: `p = 3`, `d = (3,4,4)`. That instance is `MinUPB344`
(`jig.so/p/13`), where `m = 10 = f_N + 1` is a theorem, so the statement's conclusion is not
merely consistent but attained in at least one admissible tuple.

## What is known at pose time

* Bipartite, `min(d₁,d₂) ≥ 3`: Chen–Johnston Cor. 2 — complete.
* Any `p`, largest factor dominating, `d_p − 1 ≥ Σ_{j<p}(dⱼ − 1) ≥ 3`: Chen–Johnston Thm 1.
* All factors qubits: Feng, Discrete Appl. Math. **154** (2006) 942–949, and Johnston,
  *The minimum size of qubit unextendible product bases*, TQC 2013 (= arXiv:1302.1604).
* `(2,2,4k+1)`: Chen–Johnston Thm 3. `(2,2,4k−1)`, `k ≥ 2`: `jig.so/p/6`.
* `(3,4,4)`: `jig.so/p/13`.
* Open: every system whose factors are comparable in size and which is not one of the above —
  the smallest instances being `(4,4,5)`, `(2,2,4,4)`, `(2,3,3,4)`.
* Method ceiling, and the reason the open region is hard: a family whose local factors are in
  **general position** (any `dⱼ` of the `j`-th factors independent) has at most `f_N` members,
  so the orthogonal-representation route of Alon–Lovász §3 — which produces exactly such
  families, and which every known minimum-size UPB is built from — cannot reach `f_N + 1` in
  any system. Filed as `GenPosUPBTrivialCeiling`. Every witness for this problem must
  therefore be locally degenerate, and by the same count degenerate in exactly one unit.
-/

namespace Statements.MinUPBAtMostTrivialPlusOne

/-- The canonical proposition. This is the type the verifier demands.

For every number of parties `p ≥ 2` and every list of local dimensions `dⱼ ≥ 2`, excluding
only the bipartite systems with a qubit factor (where `f_m = d₁d₂` is known and larger), there
is an unextendible product basis of `C^{d₁} ⊗ ⋯ ⊗ C^{d_p}` of cardinality at most
`f_N(d₁,…,d_p) + 1 = 2 + Σⱼ(dⱼ − 1)`: some `m` states, given by their factors, pairwise
orthogonal, all factors nonzero, with no nonzero product state orthogonal to all of them. -/
abbrev statement : Prop :=
  ∀ p : ℕ, 2 ≤ p → ∀ d : Fin p → ℕ, (∀ j, 2 ≤ d j) →
    ¬ (p = 2 ∧ ∃ j, d j = 2) →
    ∃ m : ℕ, m ≤ 2 + ∑ j, (d j - 1) ∧
      ∃ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
        (∀ i j, v i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
        (∀ a : (j : Fin p) → Fin (d j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPBAtMostTrivialPlusOne
