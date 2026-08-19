import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausOblathCriterion — 4/n when n+1 has a divisor ≡ 3 (mod 4)

## The claim

If `n ≥ 2` and `n + 1 = d * e` with `e ≡ 3 (mod 4)`, then `4/n` is a sum of three unit
fractions. Explicitly, with `F = (e+1)/4`:

`4/n = 1/(d*F) + 1/(n*d*F) + 1/(n*F)`.

Equivalently: `4/n` is representable whenever `n + 1` has any divisor congruent to
`3 (mod 4)`, hence whenever `n + 1` has a prime factor `≡ 3 (mod 4)`.

## What is NOT claimed

Nothing when `n + 1` has no such divisor. Nothing about distinctness or size of the
denominators. No converse.
-/

namespace Statements.ErdosStrausOblathCriterion

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ d e : ℕ, n + 1 = d * e → e % 4 = 3 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausOblathCriterion
