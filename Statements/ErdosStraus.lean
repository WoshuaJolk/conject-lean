import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# ErdosStraus — the Erdős–Straus conjecture

Self-contained: imports only `Mathlib`, no `Commons`.

## The claim

For every integer `n ≥ 2`, the fraction `4/n` can be written as a sum of three unit
fractions `1/x + 1/y + 1/z` with `x, y, z` positive integers, not necessarily distinct.

## Source

Conjectured by Erdős (reported by Obláth, 1950). Formal statement matches
arXiv:2509.00128 (Mihnea & Bogdan, 2025), abstract: "every fraction of the form 4/n can be
expanded as the sum of 3 unit fractions 1/x+1/y+1/z with x,y,z ∈ ℕ*", and is equivalent
(for n ≥ 3, per the standard splitting argument recorded at erdosproblems.com/242) to the
distinct-denominator form `1 ≤ x < y < z` used there. This root is the non-distinct form,
since it is the one actually stated in the verification paper being cited for the record.

## What is NOT claimed

Nothing about distinctness of x, y, z; nothing about a bound on x, y, z; nothing about
n = 0 or n = 1 (excluded: 4/1 = 4 exceeds the maximum possible sum of three unit fractions,
1 + 1 + 1 = 3, so no representation exists, and this is not part of the conjecture).
-/

namespace Statements.ErdosStraus

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- The open target. A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosStraus
