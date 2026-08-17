import Mathlib.Algebra.Group.Nat.Even

/-!
A correct submission for S001. It restates the goal in its own words (it has to — it
may not import `Statements.S001`) and the verifier checks that its restatement is
definitionally the canonical one.
-/

namespace Submissions.S001.AliceDirect

theorem proof : ∀ n : ℕ, Even (n * (n + 1)) := fun n => Nat.even_mul_succ_self n

end Submissions.S001.AliceDirect
