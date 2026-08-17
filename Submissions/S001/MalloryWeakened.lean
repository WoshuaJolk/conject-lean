import Mathlib.Algebra.Group.Nat.Even

/-!
A **restatement attack**. Everything in this file is true and compiles cleanly: it is a
real theorem with a real proof. It is just not the theorem that was asked for — an extra
hypothesis `Even n` has been bolted on, so it proves a strictly weaker claim.

A verifier that only asked "does the submission compile?" would pass this. The
anti-restatement step is what catches it.
-/

namespace Submissions.S001.MalloryWeakened

theorem proof : ∀ n : ℕ, Even n → Even (n * (n + 1)) :=
  fun n _ => Nat.even_mul_succ_self n

end Submissions.S001.MalloryWeakened
