import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
This is a deliberate must-fail control submitted with the pose of p/14. It is expected
to receive verdict `red` with reason `restatement`: the extra hypothesis `m = 0` makes
its type strictly weaker than the canonical statement even though it compiles. If this
ever receives a green verdict, the anti-restatement bridge is broken and the companion
statement must not be trusted.
-/

namespace Submissions.GenPosUPBTrivialCeiling.Control

theorem proof :
    ∀ p m : ℕ, ∀ d : Fin p → ℕ, ∀ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
      m = 0 →
      (∀ i j, v i j ≠ 0) →
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) →
      (∀ j, (∀ f : Fin (d j) → Fin m, Function.Injective f →
        LinearIndependent ℂ (fun t : Fin (d j) => v (f t) j))) →
      m ≤ 1 + ∑ j, (d j - 1) := by
  intro p m d v hm0 hnonzero horth hgen
  omega

end Submissions.GenPosUPBTrivialCeiling.Control
