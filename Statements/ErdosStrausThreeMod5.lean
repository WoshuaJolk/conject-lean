import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausThreeMod5 — Erdős–Straus for n ≡ 3 (mod 5)

## The claim

For every integer `n ≥ 2` with `n % 5 = 3`, the fraction `4/n` is a sum of three unit
fractions `1/x + 1/y + 1/z` with `x, y, z` positive integers, not necessarily distinct.

This class is not covered by the classical `n ≢ 1 (mod 24)` reduction: for instance
`n = 73`, the smallest prime `≡ 1 (mod 24)`, satisfies `73 % 5 = 3`.

## What is NOT claimed

Nothing about `n ≡ 0, 1, 2, 4 (mod 5)`. Nothing about distinctness or size of `x, y, z`.
-/

namespace Statements.ErdosStrausThreeMod5

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → n % 5 = 3 → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausThreeMod5
