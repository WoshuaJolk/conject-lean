import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocSecondMomentUnconditional — Problem 26's upper half as one spectral quantity

The same reduction as `PaleyLocSecondMomentBound`, with the two arithmetic hypotheses
discharged: nothing is assumed here about the vertex count or the degree of the Paley
1-localization.  The only input is one real number `c`.

Let `R` be any symmetric matrix on the vertex set of `G_{p,1}` that vanishes on the diagonal
and, on every edge `uv`, equals `|N(u) ∩ N(v)| - d²/m` with `m = (p-1)/2` and `d = (p-5)/4`.
Off the edges `R` is free.  If `c` dominates the top eigenvalue of `R`, then

    Commons.paleyLocTheta p  ≤  2 + √(p/2 + 4c).

Hence a bound `c = o(p)` gives `limsup ϑ(Ḡ_{p,1})/√(p/2) ≤ 1`, the upper half of
Randomstrasse101 Problem 26.  A bound `c ≤ γp` with `γ < 1/8` already beats the published
`√p`, since `c = p/8` is exactly what returns `√p`.

The quantity `c` is arithmetic, not semidefinite.  For adjacent `u, v` in `G_{p,1}` the
common-neighbour count `|N(u) ∩ N(v)|` is `p/8` plus one eighth of `∑ₐ χ(a(a-1)(x-a))`, a
Frobenius trace of the Legendre elliptic curve bounded by `2√p`; so `R` is a circulant whose
entries are Frobenius traces, and `c` is the smallest achievable top eigenvalue over all
completions of that data off the edges.

## Term-by-term read-back

* `p` prime, `p % 4 = 1`, `5 < p`.  `NeZero p` is an instance binder so that
  `Commons.PaleyLocV p` elaborates; it is implied by primality.
* `A` is pinned to the 0/1 adjacency matrix of `Commons.paleyLocAdj p` by
  `adj u v → A u v = 1` together with `¬ adj u v → A u v = 0`.  Nothing else is assumed of
  `A`; in particular its row sums are **not** hypothesised — they are computed in the proof.
* `R` — `R u u = 0` for every `u`, and `R u v = (A * A) u v - ((p-5)/4)² / ((p-1)/2)` for
  every adjacent pair.  `(A * A) u v` is the number of common neighbours.  Free off the edges.
* `(c • 1 - R).PosSemidef` — `c` dominates the top eigenvalue of `R`.
* the conclusion — `Commons.paleyLocTheta p hp.pos`, the problem's own quantity, is at most
  `2 + Real.sqrt ((p:ℝ)/2 + 4*c)`.

## What this does not say

The implication only.  Nothing is asserted about how small `c` can be made; that is the open
part.  No lower bound on `ϑ` is claimed, the existence of `lim ϑ/√p` is not assumed, and
nothing is said about Schrijver's `ϑ'`, the 2-localization, or prime-power order.  It is not
vacuous: for each such `p` the hypotheses determine `A` uniquely, and `R` may be taken to be
the deviation on the edges and `0` elsewhere with `c` its largest eigenvalue.
-/

namespace Statements.PaleyLocSecondMomentUnconditional

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p % 4 = 1 → 5 < p →
    ∀ (A R : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (c : ℝ),
      (∀ u v, Commons.paleyLocAdj p u v → A u v = 1) →
      (∀ u v, ¬ Commons.paleyLocAdj p u v → A u v = 0) →
      (∀ u, R u u = 0) →
      (∀ u v, Commons.paleyLocAdj p u v →
        R u v = (A * A) u v - (((p : ℝ) - 5) / 4) ^ 2 / (((p : ℝ) - 1) / 2)) →
      (c • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - R).PosSemidef →
      Commons.paleyLocTheta p hp.pos ≤ 2 + Real.sqrt ((p : ℝ) / 2 + 4 * c)

/-- The open target. -/
theorem target : statement := sorry

end Statements.PaleyLocSecondMomentUnconditional
