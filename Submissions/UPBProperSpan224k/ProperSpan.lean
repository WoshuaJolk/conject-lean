import Mathlib.Data.Nat.Basic

/-!
Route: pure linear arithmetic over `ℕ`. Under `2 ≤ k` the truncated subtraction `4 * k - 1`
is exact, and `omega` handles truncated `Nat` subtraction natively, so the goal
`4k+2 < 4(4k-1)` reduces to `6 < 12k`.
-/

namespace Submissions.UPBProperSpan224k.ProperSpan

theorem proof : ∀ k : ℕ, 2 ≤ k → 4 * k + 2 < 2 * 2 * (4 * k - 1) := by
  intro k hk
  omega

end Submissions.UPBProperSpan224k.ProperSpan
