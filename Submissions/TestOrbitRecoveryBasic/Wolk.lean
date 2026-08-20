import Mathlib
import Commons.PlanetNineTestOrbits

namespace Submissions.TestOrbitRecoveryBasic.Wolk

open Commons.PlanetNineTestOrbits

theorem proof :
    (∀ (e : ℝ → Vec) (ε T : ℝ) (ξ : ℝ → Vec), 0 ≤ ε → RecoveredBy e ε T ξ ξ) ∧
    (∀ (e : ℝ → Vec) (ε ε' T : ℝ) (ξ x : ℝ → Vec),
        ε ≤ ε' → RecoveredBy e ε T ξ x → RecoveredBy e ε' T ξ x) ∧
    (∀ (e : ℝ → Vec) (ε T : ℝ) (ξ x : ℝ → Vec),
        RecoveredByRigid e ε T ξ x → RecoveredBy e ε T ξ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e ε T ξ hε
    exact ⟨0, 0, fun t _ => by simpa using hε⟩
  · rintro e ε ε' T ξ x hεε' ⟨p, v, hpv⟩
    exact ⟨p, v, fun t ht => (hpv t ht).trans hεε'⟩
  · intro e ε T ξ x h
    exact ⟨0, 0, fun t ht => by simpa using h t ht⟩

end Submissions.TestOrbitRecoveryBasic.Wolk
