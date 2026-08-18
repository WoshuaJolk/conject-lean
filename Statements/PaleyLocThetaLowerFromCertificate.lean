import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocThetaLowerFromCertificate — Problem 26's lower half, from a certificate

The companion of `PaleyLocSecondMomentUnconditional`, on the other side.  Where that
statement turns an eigenvalue bound into an **upper** bound on `Commons.paleyLocTheta`, this
one turns a Lovász certificate for the **complement** of the Paley 1-localization into a
**lower** bound on the same quantity:

    paleyLocTheta p  ≥  ((p-1)/2) / θ̄,

for any symmetric `Ȳ` that is `1` on the diagonal and `1` on every distinct pair that is
*non*-adjacent in `G_{p,1}` — free on the edges — with `θ̄ · I - Ȳ ⪰ 0`.

`Ȳ` is exactly a feasible point of Lovász's dual for `ϑ` of the complement graph, so `θ̄` is
any upper bound on `ϑ_clique(Ḡ_{p,1})`.  Feeding in the ratio-bound certificate gives
`θ̄ ≈ √p` and returns the published `ϑ ≥ √p/2`; feeding in a certificate with
`θ̄ ≤ (1+o(1))√(p/2)` returns `ϑ ≥ (1-o(1))·(p/2)/√(p/2) = (1-o(1))√(p/2)`, which is the
**lower half** of Randomstrasse101 Problem 26 — the half asserting that the level-1 localized
SDP cannot beat Hanson–Petridis.

Together with `PaleyLocSecondMomentUnconditional` this reduces both halves of Problem 26 to
the quality of a second-moment certificate, one for `G_{p,1}` and one for its complement.

## The mechanism

`Ȳ` is turned into a *primal* point for `G_{p,1}` in one line: `M = θ̄·I - Ȳ + J` is positive
semidefinite (a sum of two positive semidefinite matrices, since `J = 𝟙𝟙ᵀ`), it vanishes on
every distinct non-adjacent pair of `G_{p,1}` because `Ȳ` is `1` there, its trace is `θ̄m`, and
its entry sum is at least `m²` because `𝟙ᵀ(θ̄I - Ȳ)𝟙 ≥ 0`.  Normalising by `θ̄m` gives a
feasible point of value at least `m/θ̄`.  This is the vertex-transitive half of Lovász's
`ϑ(G)ϑ(Ḡ) = n` in the only direction needed, and it needs neither vertex-transitivity nor
orthonormal representations.

## Term-by-term read-back

* `p` prime, `p % 4 = 1`, `5 < p`; `NeZero p` is an instance binder so `Commons.PaleyLocV p`
  elaborates, and is implied by primality.
* `0 < θ̄`.
* `∀ u, Ȳ u u = 1` — unit diagonal.
* `∀ u v, u ≠ v → ¬ Commons.paleyLocAdj p u v → Ȳ u v = 1` — `Ȳ` is `1` on the *non*-edges of
  `G_{p,1}`, i.e. on the edges of the complement.  On the edges of `G_{p,1}` it is free.
* `(θ̄ • 1 - Ȳ).PosSemidef` — `θ̄` dominates the largest eigenvalue of `Ȳ`.
* the conclusion — `((p:ℝ) - 1)/2/θ̄ ≤ Commons.paleyLocTheta p hp.pos`, with `(p-1)/2` the
  vertex count of `G_{p,1}`, proved inside rather than assumed.

## What this does not say

A lower bound only; nothing is claimed above.  It asserts nothing about how small `θ̄` can be
made — that is the open part.  It does not assume `lim ϑ/√p` exists, and says nothing about
Schrijver's `ϑ'`, the 2-localization, or prime-power order.  Not vacuous: `Ȳ` with `1` on the
diagonal and non-edges and `0` on the edges, together with `θ̄ = ‖Ȳ‖`, satisfies every
hypothesis.
-/

namespace Statements.PaleyLocThetaLowerFromCertificate

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p % 4 = 1 → 5 < p →
    ∀ (Ybar : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (θ : ℝ),
      0 < θ →
      (∀ u, Ybar u u = 1) →
      (∀ u v, u ≠ v → ¬ Commons.paleyLocAdj p u v → Ybar u v = 1) →
      (θ • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - Ybar).PosSemidef →
      ((p : ℝ) - 1) / 2 / θ ≤ Commons.paleyLocTheta p hp.pos

/-- The open target. -/
theorem target : statement := sorry

end Statements.PaleyLocThetaLowerFromCertificate
