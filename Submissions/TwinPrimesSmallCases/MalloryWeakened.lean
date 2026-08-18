import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

set_option maxRecDepth 100000

namespace Submissions.TwinPrimesSmallCases.MalloryWeakened

/-- DELIBERATELY WEAKENED must-fail control.  Only the count below 100 and the `(7, 9)`
guard, with a vacuous hypothesis bolted on: no list, no second count, no offset guards, no
witnesses above `10 ^ 5`.  True, kernel-checked, and not the statement that was asked. -/
theorem proof (h : (0 : ℕ) = 0) :
  ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card = 8
  ∧ (Nat.Prime 7 ∧ ¬ Nat.Prime 9) := by
  exact ⟨by decide, by decide⟩

end Submissions.TwinPrimesSmallCases.MalloryWeakened
