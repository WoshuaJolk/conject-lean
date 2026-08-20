import Mathlib
import Commons.PlanetNineTestOrbits

/-!
# TestOrbitCover — does a line finder beat the six-dimensional template bank?

Moeyens et al. (2021), *THOR: An Algorithm for Cadence-independent Asteroid Discovery*,
AJ 162:143, Section 2:

> "it is also clear this approach will leave the algorithm blind to unknown populations or
> objects on unusual orbits. We leave the problem of developing an algorithm to select the
> optimal number of orbits to exhaustively search the entire phase space for future work."

Geringer-Sameth, Golovich & Iwabuchi (2025), arXiv:2509.25428, answered the corresponding
question for *pixel stacking*: carrying Owen's gravitational-wave template-bank geometry
over to orbital parameter space, they obtain a trial-orbit density scaling as the inverse
sixth power of the point-spread width, and report that an all-sky six-year search beyond
100 au would need of order `10^19` trial orbits. Six is the dimension of orbital phase
space, and a plain Lipschitz net over initial conditions already achieves it.

Their filter must land on the object's actual pixels, so it pays for all six directions.
THOR's does not: a constant sky offset and a constant sky drift are exactly what the
downstream line finder fits, so those directions are free, in the same way Owen's
*extrinsic* parameters are maximised over rather than gridded. Nobody has computed what
that quotient buys — arXiv:2509.25428 does not treat it, and THOR quantifies no cover at
all — and everything about whether a complete distant-object search is affordable turns
on it. At the `10^19` scale, an exponent of 4 instead of 6 is a saving of about six orders
of magnitude, and an exponent of 2 is about thirteen.

The canonical proposition asks the qualitative form of that question, which is the form
that is genuinely open: does the line finder's affine freedom buy *anything* provable —
is the exponent strictly below the phase-space dimension?
-/

namespace Statements.TestOrbitCover

open Commons.PlanetNineTestOrbits

/-- The canonical proposition. This is the type the verifier demands.

For every attracting mass `μ` and every shell `[R₁, R₂]` outside the observer's orbit,
there are an exponent `d ≤ 5` and a constant `C` such that for every window `[0, T]` short
compared with the shell's orbital timescale, every tolerance `ε ∈ (0, 1]`, and every
observer on its own Kepler orbit within one length unit of the centre, the shell admits an
exhaustive cover by at most `C / ε ^ d` test orbits.

The bound is stated as `ncard * ε ^ d ≤ C` to keep it division-free. The content is the
exponent: `d = 6` is reachable by a plain Lipschitz net over initial conditions and is the
rate of the matched-filter template bank, so `d ≤ 5` asserts that the line finder's affine
freedom is worth a strict power of the tolerance. -/
abbrev statement : Prop :=
  ∀ μ R₁ R₂ : ℝ, 0 < μ → 1 < R₁ → R₁ < R₂ → μ ≤ R₁ ^ 3 →
    ∃ (d : ℕ) (C : ℝ), d ≤ 5 ∧ 0 < C ∧
      ∀ T ε : ℝ, 1 ≤ T → μ * T ^ 2 ≤ R₁ ^ 3 → 0 < ε → ε ≤ 1 →
        ∀ e : ℝ → Vec, IsObserver μ T e →
          ∃ S : Set (ℝ → Vec), S.Finite ∧
            (S.ncard : ℝ) * ε ^ d ≤ C ∧
            IsExhaustiveCover μ R₁ R₂ T ε e S

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.TestOrbitCover
