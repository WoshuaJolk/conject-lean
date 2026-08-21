import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPB344Upper14 — `f_m(3,4,4) ≤ 14`

An explicit unextendible product basis of fourteen states in `C³ ⊗ C⁴ ⊗ C⁴`, obtained by
joining a size-6 bipartite UPB in `C³ ⊗ C⁴` with a size-8 UPB in `C³ ⊗ C³ ⊗ C⁴` along the
splitting `C⁴ = C¹ ⊕ C³`. Together with the Alon–Lovász lower bound `f_m(3,4,4) ≥ 10`
recorded on the root statement `MinUPB344`, this squeezes
`10 ≤ f_m(3,4,4) ≤ 14`.
-/

namespace Statements.MinUPB344Upper14

/-- There exist `14` nonzero pairwise-orthogonal product states in `C³ ⊗ C⁴ ⊗ C⁴` that admit
no orthogonal product extension. -/
abbrev statement : Prop :=
  ∃ u : Fin 14 → Fin 3 → ℂ,
  ∃ w : Fin 14 → Fin 4 → ℂ,
  ∃ z : Fin 14 → Fin 4 → ℂ,
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

theorem target : statement := sorry

end Statements.MinUPB344Upper14
