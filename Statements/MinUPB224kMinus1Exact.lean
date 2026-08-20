import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Order.Bounds.Defs

/-!
# MinUPB224kMinus1Exact — the problem's own question, as one proposition

Problem 6 asks: *is the minimum cardinality of an unextendible product basis of
`C² ⊗ C² ⊗ C^(4k−1)` equal to `4k+2`, for every `k ≥ 2`?* This statement is that question,
asserted, and nothing else. It is `IsLeast`: `4k+2` is achievable, and nothing smaller is.

Two statements already carry the halves, both `proved`:

* `MinUPB224kMinus1` — an unextendible product basis of cardinality `4k+2` exists. An upper
  bound, `f_m ≤ 4k+2`.
* `MinUPB224kMinus1Lower` — none of cardinality `m ≤ 4k+1` exists. The matching lower bound,
  `f_m ≥ 4k+2`, formerly cited to Alon–Lovász Cor. 4.1(i) and now proved.

Between them the equality follows in one line. But *nothing in the graph elaborated that
line*: each verdict covered one inequality, and the conjunction was a claim a reader had to
assemble by hand. Assembling it by hand is exactly the step a machine-checked corpus is
supposed to remove, and it is the step where a mismatch between the two bracketed existentials
would hide — if the two halves quantified over subtly different objects, both could be green
and the equality still false. This statement closes that gap: one proposition, one verdict,
both halves forced through the same existential.

## What is and is not new here

The mathematics is entirely in the two halves; this adds none. Its submission is required by
the import policy to be self-contained — a submission may import Mathlib and `Commons`, never
another submission — so it inlines both existing proofs verbatim and pairs them. The composition
step is nine lines. Treat a green verdict here as evidence about the *fit* between the two
halves, not as a third result.

## Conventions

Those of `MinUPB224kMinus1`: a product state `|u⟩⊗|w⟩⊗|z⟩` is recorded by its three factors,
the inner product is `⟨x|y⟩ = Σ conj(xᵣ)·yᵣ`, and `⟨ψᵢ|ψⱼ⟩` is the displayed triple product.
`IsUPB k m` below is character-identical to the existential of `MinUPB224kMinus1` with the
cardinality `4k+2` replaced by a parameter `m`, which is what lets the two halves compose.
-/

namespace Statements.MinUPB224kMinus1Exact

/-- `IsUPB k m` says that `C² ⊗ C² ⊗ C^(4k−1)` contains `m` nonzero product states
`|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩` that are pairwise orthogonal and that no nonzero product state is
orthogonal to — i.e. that the cardinality `m` is achieved by some unextendible product
basis. -/
abbrev IsUPB (k m : ℕ) : Prop :=
  ∃ u : Fin m → Fin 2 → ℂ,
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

/-- The canonical proposition.

For every `k ≥ 2`, the least `m` for which `C² ⊗ C² ⊗ C^(4k−1)` has an unextendible product
basis of cardinality `m` is exactly `4k+2`. That is `f_m(2,2,4k−1) = 4k+2`: the answer to
problem 6. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k → IsLeast {m : ℕ | IsUPB k m} (4 * k + 2)

/-- The open target. A submission proves `statement` in its own module and the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPB224kMinus1Exact
