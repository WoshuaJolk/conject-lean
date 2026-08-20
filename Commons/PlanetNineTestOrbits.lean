import Mathlib

/-!
# Vocabulary for the test-orbit covering problem

Two searches for faint distant solar-system bodies use "trial" or "test" orbits, and
they pay for them differently.

*Matched-filter digital tracking* (Geringer-Sameth, Golovich & Iwabuchi 2025,
arXiv:2509.25428) stacks pixels along a trial orbit, so the trial orbit must land on the
object's actual position in every image. Every direction in the six-dimensional orbital
parameter space has to be resolved, and the trial-orbit density goes as the inverse sixth
power of the point-spread width. That is `RecoveredByRigid`.

*THOR* (Moeyens et al. 2021, AJ 162:143) instead transforms detections into the frame of
the test orbit and runs a line finder. A constant offset and a constant drift are exactly
what a line finder fits, so those directions cost nothing. That is `RecoveredBy`, the same
condition modulo an affine-in-time function of the observer's sky coordinates.

`RecoveredByRigid → RecoveredBy`, so the affine notion never needs more test orbits. How
many fewer is the open question these definitions exist to state.

Units are fixed by the observer: lengths are in units of the observer's maximum distance
from the attracting centre, so an observer satisfies `‖e t‖ ≤ 1`.
-/

namespace Commons.PlanetNineTestOrbits

open Set

/-- Physical three-space. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- `IsKeplerOn μ T x` : on the window `[0, T]` the curve `x` is twice differentiable,
never passes through the attracting centre, and obeys the Newtonian two-body equation
`x'' = -(μ / ‖x‖³) • x`. -/
def IsKeplerOn (μ T : ℝ) (x : ℝ → Vec) : Prop :=
  ∃ v : ℝ → Vec,
    (∀ t ∈ Icc (0 : ℝ) T, x t ≠ 0) ∧
    (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x (v t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt v (-(μ / ‖x t‖ ^ 3) • x t) t)

/-- `InShell R₁ R₂ T x` : the body stays in the shell `[R₁, R₂]` for the whole window. -/
def InShell (R₁ R₂ T : ℝ) (x : ℝ → Vec) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ‖x t‖ ∈ Icc R₁ R₂

/-- `IsTarget μ R₁ R₂ T x` : a body the search must not miss. -/
def IsTarget (μ R₁ R₂ T : ℝ) (x : ℝ → Vec) : Prop :=
  IsKeplerOn μ T x ∧ InShell R₁ R₂ T x

/-- Unit line of sight from an observer at `e t` to a body at `x t`. -/
noncomputable def los (e x : ℝ → Vec) (t : ℝ) : Vec :=
  ‖x t - e t‖⁻¹ • (x t - e t)

/-- `RecoveredByRigid e ε T ξ x` : the line of sight to `x` stays within `ε` of the line
of sight to the test orbit `ξ` throughout the window. This is what pixel-stacking demands:
the trial track must land on the object itself. -/
def RecoveredByRigid (e : ℝ → Vec) (ε T : ℝ) (ξ x : ℝ → Vec) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ‖los e x t - los e ξ t‖ ≤ ε

/-- `RecoveredBy e ε T ξ x` : the line of sight to `x` differs from the line of sight to
the test orbit `ξ` by an affine function of time, to within `ε`, throughout the window.

This is THOR's condition. In the frame co-moving with `ξ` the track of `x` is straight to
within `ε`, and the affine term `p + t • v` is precisely the line the downstream finder is
free to fit, so a constant offset and a constant drift are free. Everything of higher
order is what the cover still has to resolve. -/
def RecoveredBy (e : ℝ → Vec) (ε T : ℝ) (ξ x : ℝ → Vec) : Prop :=
  ∃ p v : Vec, ∀ t ∈ Icc (0 : ℝ) T,
    ‖(los e x t - los e ξ t) - (p + t • v)‖ ≤ ε

/-- The observer: a body on its own Kepler orbit about the same centre, never further
than one length unit from it. -/
def IsObserver (μ T : ℝ) (e : ℝ → Vec) : Prop :=
  IsKeplerOn μ T e ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖e t‖ ≤ 1

/-- `IsExhaustiveCover μ R₁ R₂ T ε e S` : `S` is a set of test orbits, each itself a body
of the population being searched, such that every target in the shell is recovered by one
of them at tolerance `ε`. Nothing in the shell is invisible to the search. -/
def IsExhaustiveCover (μ R₁ R₂ T ε : ℝ) (e : ℝ → Vec) (S : Set (ℝ → Vec)) : Prop :=
  (∀ ξ ∈ S, IsTarget μ R₁ R₂ T ξ) ∧
  ∀ x, IsTarget μ R₁ R₂ T x → ∃ ξ ∈ S, RecoveredBy e ε T ξ x

end Commons.PlanetNineTestOrbits
