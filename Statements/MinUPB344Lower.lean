import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB344Lower — the lower bound `f_m(3,4,4) ≥ 10`, formalised

`MinUPB344`, the root statement of this problem, records the EXISTENCE half: ten
pairwise-orthogonal nonzero product states in `C³ ⊗ C⁴ ⊗ C⁴` that no nonzero product state is
orthogonal to. On its own that is an upper bound, `f_m(3,4,4) ≤ 10`. The matching lower bound
was cited in the problem's scope and deliberately left out of scope there:

> Alon & Lovász, *Unextendible product bases*, J. Combin. Theory Ser. A **95** (2001) 169–179,
> Corollary 4.1(i) — if at least one `kᵢ` is even and `n = 1 + Σ(kᵢ−1)` is odd then
> `f_m(k₁,…,k_m) > n`.

For `(3,4,4)` we have `n = 1 + 2 + 3 + 3 = 9`, which is odd, and `k₂ = 4`, which is even; so the
corollary gives `f_m(3,4,4) ≥ 10`.

**This statement is that lower bound**, in the form "no unextendible orthogonal product set of
`C³ ⊗ C⁴ ⊗ C⁴` has cardinality `m` for any `m ≤ 9`". Together with `MinUPB344` it makes
`f_m(3,4,4) = 10` a fully formal equality, with nothing left cited.

## Why this is provable without Alon–Lovász Theorem 3.1

Alon–Lovász derive Corollary 4.1 from their Theorem 3.1, on orthogonal representations and
connected edge colourings of `Kₙ`; formalising that in general is a large job, and it is not
needed at these dimensions. Everything follows from one linear-algebra fact — fewer than `d`
linear conditions on `Cᵈ` always admit a nonzero solution — used twice.

* **No `m ≤ 8`.** Split the states into blocks of sizes `≤ 2`, `≤ 3`, `≤ 3`. Choose `a ≠ 0`
  orthogonal to the `C³` factors of the first block (two conditions in dimension three), `b ≠ 0`
  orthogonal to the `C⁴` factors of the second, `c ≠ 0` for the third. Then `a ⊗ b ⊗ c` is
  orthogonal to every state, contradicting unextendibility.
* **Degree bounds at `m = 9`.** For `a ≠ 0` put `A(a) = {l : ⟨u_l,a⟩ = 0}`. If `|A(a)| ≥ 3` then
  at most six states remain, and they split into a block of `≤ 3` killed by some `b ≠ 0` and a
  block of `≤ 3` killed by some `c ≠ 0`, again contradicting unextendibility. So `|A(a)| ≤ 2`,
  and symmetrically `|B(b)| ≤ 3` and `|C(c)| ≤ 3` for the two `C⁴` factors — there the surviving
  five states split as `≤ 2` (killed on `C³`) plus `≤ 3`.
* **Tightness.** Take `a = u_i`, `b = w_i`, `c = z_i`. Self-inner-products are nonzero, so `i`
  belongs to none of the three sets, while pairwise orthogonality puts each of the other eight
  states in at least one of them. As `2 + 3 + 3 = 8`, all three bounds are attained: in
  particular exactly three states are orthogonal to `i` on the second factor, for every `i`.
* **Parity.** So `{(i,j) : i ≠ j, ⟨w_i,w_j⟩ = 0}` has `9 · 3 = 27` elements, yet it is symmetric
  and fixed-point-free under swapping, hence of even cardinality. Contradiction.

The parity contradiction is Alon–Lovász's; the route to the tight degree count is not. In graph
language: a size-nine UPB would force the second factor's orthogonality graph to be `3`-regular
on nine vertices, which the handshake lemma forbids.

## Reading the formalisation

Conventions are those of `MinUPB344`: a product state `|u⟩⊗|w⟩⊗|z⟩` is recorded by its three
factors, the inner product is `⟨x|y⟩ = Σ conj(xᵣ)·yᵣ`, conjugate-linear in the first slot, and
`⟨ψᵢ|ψⱼ⟩` is the displayed triple product. The bracketed existential is verbatim that of
`MinUPB344` with the cardinality `10` replaced by a general `m ≤ 9`; this statement asserts it is
empty. The properness-of-span clause is not restated: this statement claims nonexistence, so
omitting a requirement only makes the claim stronger.
-/

namespace Statements.MinUPB344Lower

/-- The canonical proposition.

For every `m ≤ 9` there is no family of `m` nonzero product states `|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩ ∈
C³ ⊗ C⁴ ⊗ C⁴` that is pairwise orthogonal and that no nonzero product state is orthogonal to.
Equivalently `f_m(3,4,4) ≥ 10`. -/
abbrev statement : Prop :=
  ∀ m : ℕ, m ≤ 9 →
    ¬ ∃ u : Fin m → Fin 3 → ℂ,
      ∃ w : Fin m → Fin 4 → ℂ,
      ∃ z : Fin m → Fin 4 → ℂ,
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

/-- The open target. A submission proves `statement` in its own module and the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPB344Lower
