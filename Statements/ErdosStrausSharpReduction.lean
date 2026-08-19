import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Prime.Basic

/-!
# ErdosStrausSharpReduction — Erdős–Straus reduced to a sparse set of primes

## The claim

The Erdős–Straus conjecture is EQUIVALENT to its restriction to primes `p` satisfying all
three of

* `p ≡ 1 (mod 24)`,
* `p ≢ 3 (mod 5)`,
* no divisor of `p + 1` is `≡ 3 (mod 4)`.

The right-hand side of the equivalence is verbatim the proposition of
`Statements.ErdosStraus.statement`, so proving the restricted claim proves the conjecture.

## What is NOT claimed

Neither side is asserted. This is a reduction, not a proof. The restricted set is nonempty:
`337` is prime, `337 % 24 = 1`, `337 % 5 = 2`, and the divisors of `338 = 2 · 13²` are
`1, 2, 13, 26, 169, 338`, none of which is `≡ 3 (mod 4)`.
-/

namespace Statements.ErdosStrausSharpReduction

/-- The canonical proposition. -/
abbrev statement : Prop :=
  (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      (∀ e : ℕ, e ∣ (p + 1) → e % 4 ≠ 3) →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
    (∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ))

theorem target : statement := sorry

end Statements.ErdosStrausSharpReduction
