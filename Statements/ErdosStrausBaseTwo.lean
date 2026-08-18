import Mathlib.Data.Rat.Cast.Defs

/-!
# ErdosStrausBaseTwo — the n = 2 base case of the Erdős–Straus conjecture

Self-contained. This is the smoke-test statement for `ErdosStraus`: a single small,
already-true instance in the same vocabulary, used to exercise the pipeline before the
root (which is the open conjecture and cannot itself be proved).
-/

namespace Statements.ErdosStrausBaseTwo

/-- The canonical proposition: 4/2 is a sum of three unit fractions. -/
abbrev statement : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (2 : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem target : statement := sorry

end Statements.ErdosStrausBaseTwo
