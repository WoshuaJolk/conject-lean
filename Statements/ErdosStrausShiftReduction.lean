import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Prime.Basic

/-!
# ErdosStrausShiftReduction — Erdős–Straus reduced to shift-free primes

## The claim

The Erdős–Straus conjecture is EQUIVALENT to its restriction to primes `p` satisfying

* `p ≡ 1 (mod 24)`,
* `p ≢ 3 (mod 5)`, and
* no shift `p + a` (`a ≥ 1`) has a divisor `g` with `4a ∣ g + 1`.

The right-hand side of the equivalence is verbatim the proposition of
`Statements.ErdosStraus.statement`.

## What is NOT claimed

Neither side is asserted. This is a reduction, not a proof. The restricted set is not known
here to be infinite; it is nonempty as far as search goes — `409` and `577` admit no such
shift for any `a ≤ 20000` — but no proof that the set is nonempty is offered, and none is
needed for the equivalence.
-/

namespace Statements.ErdosStrausShiftReduction

/-- The canonical proposition. -/
abbrev statement : Prop :=
  (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      (∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m → p + a = b * g → g + 1 ≠ 4 * a * m) →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
    (∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ))

theorem target : statement := sorry

end Statements.ErdosStrausShiftReduction
