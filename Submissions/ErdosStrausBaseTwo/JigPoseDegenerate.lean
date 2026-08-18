import Mathlib.Tactic.NormNum

namespace Submissions.ErdosStrausBaseTwo.JigPoseDegenerate

/-- Degenerate-hunter attack: "weakened hypothesis" from `fleet.md`'s catalogue. Proves
the base case, but under an extra vacuous hypothesis that the canonical statement does
not carry, so the type is not defeq to `Statements.ErdosStrausBaseTwo.statement` and the
anti-restatement bridge must fail. Filed with `expect: "red"`, `expect_reason:
"restatement"`. -/
theorem proof : (1 : ℕ) = 1 → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (2 : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  intro _
  refine ⟨1, 2, 2, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Submissions.ErdosStrausBaseTwo.JigPoseDegenerate
