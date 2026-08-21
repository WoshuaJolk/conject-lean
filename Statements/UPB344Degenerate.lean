import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fin.VecNotation

/-!
# UPB344Degenerate — the residual of the general-position route on `MinUPB344`

`MinUPB344` asks for ten pairwise-orthogonal nonzero product states in `C³ ⊗ C⁴ ⊗ C⁴`
that no nonzero product state is orthogonal to. Every known construction of a
minimum-size UPB puts the local families in **general position** — every `dⱼ` of the
`j`-th factors linearly independent — because that is exactly what the orthogonal
representation method of Alon–Lovász (via Lovász–Saks–Schrijver) delivers, and it is
what makes unextendibility automatic.

`GenPosUPB344Dead` kills that route at cardinality ten. This statement is what
survives it: the same existence question, restricted to local families that are
**not** in general position. It is open.
-/

namespace Statements.UPB344Degenerate

/-- General position in the `3`-dimensional factor: any three distinct indices carry
linearly independent local vectors. -/
abbrev GenPos3 (u : Fin 10 → Fin 3 → ℂ) : Prop :=
  ∀ i j k : Fin 10, i ≠ j → i ≠ k → j ≠ k → LinearIndependent ℂ ![u i, u j, u k]

/-- General position in a `4`-dimensional factor: any four distinct indices carry
linearly independent local vectors. -/
abbrev GenPos4 (x : Fin 10 → Fin 4 → ℂ) : Prop :=
  ∀ i j k l : Fin 10, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    LinearIndependent ℂ ![x i, x j, x k, x l]

/-- The canonical proposition.

There exist `10` nonzero product states `|uᵢ⟩ ⊗ |wᵢ⟩ ⊗ |zᵢ⟩ ∈ C³ ⊗ C⁴ ⊗ C⁴` which are
pairwise orthogonal, which no nonzero product state is orthogonal to, and whose local
families are **not** all in general position. The first four clauses and the
unextendibility clause are those of `MinUPB344`, verbatim; the last clause is the
negation of general position. -/
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
        (∑ r, star (z i r) * c r) ≠ 0) ∧
    ¬ (GenPos3 u ∧ GenPos4 w ∧ GenPos4 z)

/-- The open target. -/
theorem target : statement := sorry

end Statements.UPB344Degenerate
