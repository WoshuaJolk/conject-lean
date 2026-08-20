import Mathlib
import Commons.PlanetNineTestOrbits

/-!
A **restatement attack** on `Statements.TestOrbitRecoveryBasic`. Everything here is true
and compiles: it is a real theorem with a real proof. It is just not the theorem that was
asked for. Two hypotheses have been quietly strengthened — `ε ≤ ε'` to `ε = ε'` in the
monotonicity conjunct, and `ξ = x` bolted onto the rigid-to-affine bridge — which makes
both conjuncts vacuous while leaving a proposition that looks the same at a glance. The
whole content of the lemma is gone and every line still typechecks.

A verifier that only asked "does the submission compile?" would pass this.
-/

namespace Submissions.TestOrbitRecoveryBasic.MalloryEqTolerance

open Commons.PlanetNineTestOrbits

theorem proof :
    (∀ (e : ℝ → Vec) (ε T : ℝ) (ξ : ℝ → Vec), 0 ≤ ε → RecoveredBy e ε T ξ ξ) ∧
    (∀ (e : ℝ → Vec) (ε ε' T : ℝ) (ξ x : ℝ → Vec),
        ε = ε' → RecoveredBy e ε T ξ x → RecoveredBy e ε' T ξ x) ∧
    (∀ (e : ℝ → Vec) (ε T : ℝ) (ξ x : ℝ → Vec),
        ξ = x → RecoveredByRigid e ε T ξ x → RecoveredBy e ε T ξ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e ε T ξ hε
    exact ⟨0, 0, fun t _ => by simpa using hε⟩
  · rintro e ε ε' T ξ x rfl h
    exact h
  · rintro e ε T ξ x rfl h
    exact ⟨0, 0, fun t ht => by simpa using h t ht⟩

end Submissions.TestOrbitRecoveryBasic.MalloryEqTolerance
