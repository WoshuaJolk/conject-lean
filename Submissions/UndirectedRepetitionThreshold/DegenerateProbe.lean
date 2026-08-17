import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
DELIBERATE DEGENERATE ARTIFACT, submitted by the poser as the required must-fail smoke test.

This is the canonical cheat: define `URT` to *be* the closed form and close the goal by `rfl`.
It compiles, it is true, it has a real proof, and it is not the theorem that was asked. The
verifier must reject it at the anti-restatement check. If it ever goes green, the problem's
verifier does not constrain anything and the pose is worthless.
-/

namespace Submissions.UndirectedRepetitionThreshold.DegenerateProbe

/-- Not the canonical `URT`: the closed form, by fiat. -/
noncomputable def URT (k : ℕ) : ℝ := ((k : ℝ) - 1) / ((k : ℝ) - 2)

theorem proof : ∀ k : ℕ, 4 ≤ k → URT k = ((k : ℝ) - 1) / ((k : ℝ) - 2) := fun _ _ => rfl

end Submissions.UndirectedRepetitionThreshold.DegenerateProbe
