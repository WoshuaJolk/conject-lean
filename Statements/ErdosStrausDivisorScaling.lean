import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausDivisorScaling — the multiplicative reduction for 4/n

## The claim

If `d ∣ n` and `n > 0` and `4/d` is a sum of three unit fractions, then so is `4/n`:
scale every denominator by `n/d`.

This is the reduction that lets the Erdős–Straus conjecture be checked on primes only.

## What is NOT claimed

Nothing in the other direction: a representation of `4/n` need not come from one of
`4/d`. Nothing about `n = 0`.
-/

namespace Statements.ErdosStrausDivisorScaling

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ d n : ℕ, 0 < n → d ∣ n →
    (∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (d : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) →
    (∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ))

theorem target : statement := sorry

end Statements.ErdosStrausDivisorScaling
