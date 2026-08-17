import Mathlib.Algebra.Group.Nat.Even

/-!
An **empty submission**. The type is exactly right, so the anti-restatement step passes;
the axiom audit is what catches it, because `sorryAx` is not in the allowed set.
-/

namespace Submissions.S001.TrentSorry

theorem proof : ∀ n : ℕ, Even (n * (n + 1)) := by
  sorry

end Submissions.S001.TrentSorry
