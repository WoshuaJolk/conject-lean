import Mathlib.Algebra.Group.Nat.Even

/-!
A second correct submission that takes a different route: it starts from
`Even ((n+1) * ((n+1) - 1))` and commutes. Same theorem, genuinely different proof term,
so it must produce a different `elaborated_term_hash` than `AliceDirect`.
-/

namespace Submissions.S001.BobIndirect

private theorem shifted (n : ℕ) : Even ((n + 1) * ((n + 1) - 1)) :=
  Nat.even_mul_pred_self (n + 1)

theorem proof : ∀ n : ℕ, Even (n * (n + 1)) := by
  intro n
  simpa [Nat.mul_comm] using shifted n

end Submissions.S001.BobIndirect
