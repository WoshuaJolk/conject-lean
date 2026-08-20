import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB224kMinus1Lower — the lower bound `f_m(2,2,4k−1) ≥ 4k+2`, formalised

`MinUPB224kMinus1` records the EXISTENCE half of Chen–Johnston open case (1): for every
`k ≥ 2` there is an unextendible product basis of cardinality `4k+2` in
`C² ⊗ C² ⊗ C^(4k−1)`. On its own that is an upper bound, `f_m(2,2,4k−1) ≤ 4k+2`. The matching
lower bound was cited there and deliberately left out of scope:

> Alon & Lovász, *Unextendible product bases*, J. Combin. Theory Ser. A **95** (2001) 169–179,
> Corollary 4.1(i) — if at least one `kᵢ` is even and `n = 1 + Σ(kᵢ−1)` is odd then
> `f_m(k₁,…,k_m) > n`.

For `(2,2,4k−1)` we have `n = 1 + 1 + 1 + (4k−2) = 4k+1`, which is odd, and `k₁ = 2`, which is
even; so the corollary gives `f_m(2,2,4k−1) ≥ 4k+2`.

**This statement is that lower bound**, in the form "no unextendible orthogonal product set of
`C² ⊗ C² ⊗ C^(4k−1)` has cardinality `m` for any `m ≤ 4k+1`". Together with
`MinUPB224kMinus1` it makes `f_m(2,2,4k−1) = 4k+2` a fully formal equality for every `k ≥ 2`,
with nothing left cited.

## Why this is provable without Alon–Lovász Theorem 3.1

Alon–Lovász derive Corollary 4.1 from their Theorem 3.1, the statement that `f_m = n` forces
`Kₙ` to carry an `(n−k₁,…,n−k_m)`-connected edge colouring. That is a genuine theorem about
orthogonal representations and graph connectivity, and formalising it in general is a large
job. It is not needed here. Their argument uses connectivity only to reach the intermediate
fact that **each vertex meets exactly `kᵢ−1` edges of colour `i`**, and at `d₁ = d₂ = 2` that
fact follows from a direct count instead:

* Unextendibility says that for nonzero `a, b` the states missed on the first two factors,
  `A(a) = {l : ⟨u_l,a⟩ = 0}` and `B(b) = {l : ⟨w_l,b⟩ = 0}`, must leave at least `4k−1` states
  behind, since fewer than `dim` linear conditions on `C^(4k−1)` always admit a nonzero
  solution. So `|A(a) ∪ B(b)| ≤ m − (4k−1)`.
* Hence `|A(a)| ≤ 1` for every nonzero `a`: two states in `A(a)` plus one more killed by a
  suitable `b` would remove three, which is already too many. The `u`-directions are therefore
  pairwise non-parallel, and likewise the `w`-directions.
* With all classes singletons, every pair `{i,j}` is realisable as `A(a) ∪ B(b)`, which forces
  `m ≥ (4k−1) + 2`, so `m = 4k+1` exactly, and gives: for `i ≠ j` and any nonzero `c` some
  `l ∉ {i,j}` has `⟨z_l,c⟩ ≠ 0`.
* Taking `c = z_i` in that last fact shows each `z_i` is non-orthogonal to at least two other
  `z_l`, so at most `4k−2` of the `4k` remaining states are orthogonal to `i` on the third
  factor.
* Every other state must be orthogonal to `i` somewhere, and `1 + 1 + (4k−2) = 4k` is exactly
  the number of them. The three counts are therefore all tight, so **every** state has exactly
  one partner orthogonal to it on the first factor.
* That partner map is a fixed-point-free involution on `4k+1` states, and `4k+1` is odd.

The parity contradiction is Alon–Lovász's; the route to the tight degree count is not.

## Reading the formalisation

Conventions are those of `MinUPB224kMinus1`: a product state `|u⟩⊗|w⟩⊗|z⟩` is recorded by its
three factors, the inner product is `⟨x|y⟩ = Σ conj(xᵣ)·yᵣ`, and `⟨ψᵢ|ψⱼ⟩` is the displayed
triple product. The bracketed existential is verbatim that of `MinUPB224kMinus1` with `4k+2`
replaced by a general `m ≤ 4k+1`; this statement asserts it is empty.

Note that the properness clause is again not needed, and for a stronger reason than there:
this statement claims nonexistence, so omitting a requirement only makes the claim stronger.
-/

namespace Statements.MinUPB224kMinus1Lower

/-- The canonical proposition.

For every `k ≥ 2` and every `m ≤ 4k+1` there is no family of `m` nonzero product states
`|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩ ∈ C² ⊗ C² ⊗ C^(4k−1)` that is pairwise orthogonal and that no nonzero
product state is orthogonal to. Equivalently `f_m(2,2,4k−1) ≥ 4k+2`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ m : ℕ, m ≤ 4 * k + 1 →
    ¬ ∃ u : Fin m → Fin 2 → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ,
      ∃ z : Fin m → Fin (4 * k - 1) → ℂ,
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

/-- The open target. A submission proves `statement` in its own module and the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPB224kMinus1Lower
