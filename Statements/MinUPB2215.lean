import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB2215 — case `k = 4` of `MinUPB224kMinus1`

The `k = 4` instance of problem `MinUPB224kMinus1`: there is an unextendible product basis of
cardinality `18` in `C² ⊗ C² ⊗ C^15`. Together with the published lower bound
`f_m(2,2,15) ≥ 18` (Alon–Lovász, JCTA **95** (2001) 169–179, Corollary 4.1(i), applied with
`n = 1+1+1+14 = 17` odd and `k₁ = 2` even) this says `f_m(2,2,15) = 18`.

The cardinality `18` and the third local dimension `15` are `4k+2` and `4k−1` at `k = 4`, so
this proposition is the `k = 4` instance of the root, with the numerals already reduced.

Unextendibility is the whole content: the 18 states are required to admit **no** nonzero
product state orthogonal to all of them. Naively that is a search over `3^18` assignments of
the 18 indices to the three tensor factors, which is not how it is proved.
-/

namespace Statements.MinUPB2215

/-- The canonical proposition: an unextendible product basis of cardinality `18` exists in
`C² ⊗ C² ⊗ C^15`. -/
abbrev statement : Prop :=
  ∃ u : Fin 18 → Fin 2 → ℂ, ∃ w : Fin 18 → Fin 2 → ℂ, ∃ z : Fin 18 → Fin 15 → ℂ,
    (∀ i, u i ≠ 0) ∧
    (∀ i, w i ≠ 0) ∧
    (∀ i, z i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∑ r, star (u i r) * u j r) *
      (∑ r, star (w i r) * w j r) *
      (∑ r, star (z i r) * z j r) = 0) ∧
    (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 → ∀ c : Fin 15 → ℂ, c ≠ 0 →
      ∃ i,
        (∑ r, star (u i r) * a r) *
        (∑ r, star (w i r) * b r) *
        (∑ r, star (z i r) * c r) ≠ 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.MinUPB2215
