import Mathlib.Data.Nat.Basic

namespace Submissions.UPBProperSpan344.SmokeRed

-- Wrong: proves ≤ instead of <  (or True). Anti-restatement / type mismatch should red.
theorem proof : 10 ≤ 3 * 4 * 4 := by decide

end Submissions.UPBProperSpan344.SmokeRed
