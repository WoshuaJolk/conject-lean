import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStrausOutside1Mod24 — Erdős–Straus outside the class 1 mod 24

## The claim

For every integer `n ≥ 2` with `n % 24 ≠ 1`, the fraction `4/n` is a sum of three
unit fractions `1/x + 1/y + 1/z` with `x, y, z` positive integers, not necessarily
distinct.

This is the unconditional part of the classical reduction of the Erdős–Straus
conjecture: only the residue class `1 (mod 24)` survives.

## What is NOT claimed

Nothing about `n ≡ 1 (mod 24)`, which is exactly the open part of the conjecture.
Nothing about distinctness or size of `x, y, z`.
-/

namespace Statements.ErdosStrausOutside1Mod24

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → n % 24 ≠ 1 → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausOutside1Mod24
