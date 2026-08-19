import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Prime.Basic

/-!
# ErdosStrausPrimeReduction — Erdős–Straus reduced to primes ≡ 1 (mod 24), ≢ 3 (mod 5)

## The claim

The Erdős–Straus conjecture (`∀ n ≥ 2, 4/n = 1/x + 1/y + 1/z` with `x, y, z` positive
integers) is EQUIVALENT to its restriction to prime `p` with `p % 24 = 1` and
`p % 5 ≠ 3`.

The right-hand side of the equivalence is verbatim the proposition of
`Statements.ErdosStraus.statement`, so a proof of the restricted claim yields the
full conjecture.

## What is NOT claimed

Neither side is asserted. This is a reduction, not a proof of the conjecture. The
residual class is nonempty: `97` is the smallest prime `≡ 1 (mod 24)` with
`p % 5 ≠ 3`.
-/

namespace Statements.ErdosStrausPrimeReduction

/-- The canonical proposition. -/
abbrev statement : Prop :=
  (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
    (∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ))

theorem target : statement := sorry

end Statements.ErdosStrausPrimeReduction
