import Mathlib
import Commons.PlanetNineTestOrbits

/-!
# TestOrbitRecoveryBasic — the bridge from rigid recovery to line-finder recovery

Three facts about `RecoveredBy` that every covering argument for
`Statements.TestOrbitCover` uses and none of them states.

Reflexivity is what makes covers exist at all: a test orbit recovers itself, so a finite
set of targets is covered by itself. Monotonicity in `ε` is what makes coarse-to-fine
search sound. The third is the bridge to the published matched-filter result: rigid
recovery implies line-finder recovery, so any pixel-stacking template bank is already a
THOR cover of the same size. That is the sense in which the exponent 6 of
Geringer-Sameth, Golovich & Iwabuchi (2025), arXiv:2509.25428, is an upper bound for the
problem posed here, and the reason the open question is whether it can be beaten rather
than whether it can be attained.
-/

namespace Statements.TestOrbitRecoveryBasic

open Commons.PlanetNineTestOrbits

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  (∀ (e : ℝ → Vec) (ε T : ℝ) (ξ : ℝ → Vec), 0 ≤ ε → RecoveredBy e ε T ξ ξ) ∧
  (∀ (e : ℝ → Vec) (ε ε' T : ℝ) (ξ x : ℝ → Vec),
      ε ≤ ε' → RecoveredBy e ε T ξ x → RecoveredBy e ε' T ξ x) ∧
  (∀ (e : ℝ → Vec) (ε T : ℝ) (ξ x : ℝ → Vec),
      RecoveredByRigid e ε T ξ x → RecoveredBy e ε T ξ x)

/-- The open target. A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TestOrbitRecoveryBasic
