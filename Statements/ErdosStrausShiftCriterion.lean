import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausShiftCriterion — a shifted-divisor sufficient condition for 4/n

## The claim

If `n ≥ 2` and there are positive `a, b, m` and a natural `g` with

* `n + a = b * g`, and
* `g + 1 = 4 * a * m`,

then `4/n = 1/(a*b*m) + 1/(n*b*m) + 1/(n*a*m)`.

In words: `4/n` is representable whenever some shift `n + a` has a divisor `g` with
`4a ∣ g + 1`. The case `a = 1` is Oblath's criterion (`n + 1` has a divisor `≡ 3 mod 4`);
`a = 2` gives divisors of `n + 2` that are `≡ 7 mod 8`, `a = 3` gives divisors of `n + 3`
that are `≡ 11 mod 12`, and so on.

## What is NOT claimed

Nothing when no such `a, b, g, m` exist, and no converse: a representation of `4/n` need not
have this shape.
-/

namespace Statements.ErdosStrausShiftCriterion

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n a b g m : ℕ, 2 ≤ n → 0 < a → 0 < b → 0 < m →
    n + a = b * g → g + 1 = 4 * a * m →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausShiftCriterion
