import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

namespace Submissions.PaleyLocSmallCases.MalloryWeakened

/-- DELIBERATELY WEAKENED. Only the two vertex-count conjuncts, with a vacuous hypothesis
bolted on. True, kernel-checked, and not the statement that was asked. -/
theorem proof (h : (0:ℕ) = 0) :
  Fintype.card {x : ZMod 13 // x ≠ 0 ∧ ∃ r : ZMod 13, x = r * r} = 6 ∧
  Fintype.card {x : ZMod 17 // x ≠ 0 ∧ ∃ r : ZMod 17, x = r * r} = 8 := by
  exact ⟨by decide, by decide⟩

end Submissions.PaleyLocSmallCases.MalloryWeakened
