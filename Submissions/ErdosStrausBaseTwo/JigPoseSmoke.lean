import Mathlib.Tactic.NormNum

namespace Submissions.ErdosStrausBaseTwo.JigPoseSmoke

/-- 4/2 = 1/1 + 1/2 + 1/2. -/
theorem proof : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (2 : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  refine ⟨1, 2, 2, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Submissions.ErdosStrausBaseTwo.JigPoseSmoke
