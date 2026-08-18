import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# MinUPB227 — case `k = 2` of `MinUPB224kMinus1`

The `k = 2` instance of problem `MinUPB224kMinus1`: there is an unextendible product basis of
cardinality `10` in `C² ⊗ C² ⊗ C^7`. Together with the published lower bound
`f_m(2,2,7) ≥ 10` (Alon–Lovász, JCTA **95** (2001) 169–179, Corollary 4.1(i), applied with
`n = 1+1+1+6 = 9` odd and `k₁ = 2` even) this says `f_m(2,2,7) = 10` — the smallest case
Chen–Johnston list as open in §6 of Commun. Math. Phys. **333** (2015) 351–365.

The cardinality `10` and the third local dimension `7` are `4k+2` and `4k−1` at `k = 2`, so
this proposition is the `k = 2` instance of the root, with the numerals already reduced.

Unextendibility is the whole content: the ten states are required to admit **no** nonzero
product state orthogonal to all of them. Naively that is a search over `3^10 = 59049`
assignments of the ten indices to the three tensor factors. It is not proved that way here —
see `Submissions/MinUPB227/` for the pruned form, which is `77` branches each closed by an
explicit `7 × 7` inverse.
-/

namespace Statements.MinUPB227

/-- The canonical proposition: an unextendible product basis of cardinality `10` exists in
`C² ⊗ C² ⊗ C^7`. -/
abbrev statement : Prop :=
  ∃ u : Fin 10 → Fin 2 → ℂ, ∃ w : Fin 10 → Fin 2 → ℂ, ∃ z : Fin 10 → Fin 7 → ℂ,
    (∀ i, u i ≠ 0) ∧
    (∀ i, w i ≠ 0) ∧
    (∀ i, z i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∑ r, star (u i r) * u j r) *
      (∑ r, star (w i r) * w j r) *
      (∑ r, star (z i r) * z j r) = 0) ∧
    (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 → ∀ c : Fin 7 → ℂ, c ≠ 0 →
      ∃ i,
        (∑ r, star (u i r) * a r) *
        (∑ r, star (w i r) * b r) *
        (∑ r, star (z i r) * c r) ≠ 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.MinUPB227
