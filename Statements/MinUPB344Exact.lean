import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Order.Bounds.Defs

/-!
# MinUPB344Exact — the problem's own question, as one proposition

Problem 13 asks: *is the minimum cardinality of an unextendible product basis of
`C³ ⊗ C⁴ ⊗ C⁴` equal to 10?* This statement is that question, asserted, and nothing else. It is
`IsLeast`: `10` is achievable, and nothing smaller is.

Two statements carry the halves:

* `MinUPB344` — an unextendible product basis of cardinality `10` exists. An upper bound,
  `f_m ≤ 10`. Proved: an explicit integer witness whose three orthogonality graphs are the
  Petersen graph and a `3`-factorisation of its complement.
* `MinUPB344Lower` — none of cardinality `m ≤ 9` exists. The matching lower bound, `f_m ≥ 10`,
  formerly cited to Alon–Lovász Cor. 4.1(i).

Between them the equality follows in one line. But nothing in the graph elaborates that line:
each verdict covers one inequality, and the conjunction is a claim a reader has to assemble by
hand — which is where a mismatch between the two bracketed existentials would hide. If the two
halves quantified over subtly different objects, both could be green and the equality still
false. This statement closes that gap: one proposition, one verdict, both halves forced through
the same existential.

## What is and is not new here

The mathematics is entirely in the two halves; this adds none. Its submission is required by the
import policy to be self-contained — a submission may import Mathlib and `Commons`, never another
submission — so it inlines both proofs and pairs them. Treat a green verdict here as evidence
about the *fit* between the two halves, not as a third result.

## Conventions

Those of `MinUPB344`: a product state `|u⟩⊗|w⟩⊗|z⟩` is recorded by its three factors, the inner
product is `⟨x|y⟩ = Σ conj(xᵣ)·yᵣ`, conjugate-linear in the first slot, and `⟨ψᵢ|ψⱼ⟩` is the
displayed triple product. `IsUPB m` below is character-identical to the existential of
`MinUPB344` with the cardinality `10` replaced by a parameter `m`, which is what lets the two
halves compose. Properness of the span is automatic at these parameters (`m ≤ 10 < 48`) and is
not restated.
-/

namespace Statements.MinUPB344Exact

/-- `IsUPB m` says that `C³ ⊗ C⁴ ⊗ C⁴` contains `m` nonzero product states
`|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩` that are pairwise orthogonal and that no nonzero product state is
orthogonal to — i.e. that the cardinality `m` is achieved by some unextendible product basis. -/
abbrev IsUPB (m : ℕ) : Prop :=
  ∃ u : Fin m → Fin 3 → ℂ,
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

/-- The canonical proposition.

The least `m` for which `C³ ⊗ C⁴ ⊗ C⁴` has an unextendible product basis of cardinality `m` is
exactly `10`. That is `f_m(3,4,4) = 10`: the answer to problem 13. -/
abbrev statement : Prop := IsLeast {m : ℕ | IsUPB m} 10

/-- The open target. A submission proves `statement` in its own module and the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.MinUPB344Exact
