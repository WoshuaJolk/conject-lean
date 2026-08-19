import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausSplitCriterion — a divisor-splitting sufficient condition for 4/n

## The claim

If `4x = n + a + b` and `a * y = n * x` and `b * z = n * x` for positive `x, y, z`,
then `4/n = 1/x + 1/y + 1/z`.

The mechanism: `1/y = a/(nx)`, `1/z = b/(nx)`, `1/x = n/(nx)`, so the three unit
fractions sum to `(n+a+b)/(nx) = 4x/(nx) = 4/n`.

## What is NOT claimed

Nothing about the existence of such `a, b, x, y, z` for any given `n`; this is a
sufficient condition only, supplying a representation once a splitting is exhibited.
-/

namespace Statements.ErdosStrausSplitCriterion

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n a b x y z : ℕ, 0 < n → 0 < x → 0 < y → 0 < z →
    a * y = n * x → b * z = n * x → 4 * x = n + a + b →
    ∃ p q r : ℕ, 0 < p ∧ 0 < q ∧ 0 < r ∧
      (4 : ℚ) / (n : ℚ) = 1 / (p : ℚ) + 1 / (q : ℚ) + 1 / (r : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausSplitCriterion
