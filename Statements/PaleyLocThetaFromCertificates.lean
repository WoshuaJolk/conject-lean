import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocThetaFromCertificates — a sufficient condition for Problem 26

This is the capstone of the second-moment route: a single implication whose conclusion is
**verbatim the root statement of this problem**, and whose two hypotheses are estimates about
certificates rather than about `ϑ` itself.

* **Hypothesis A** asks, for every `δ > 0` and all large `p ≡ 1 (mod 4)`, for a symmetric `R`
  vanishing on the diagonal and equal to `|N(u) ∩ N(v)| - d²/m` on every edge of `G_{p,1}`
  (free off the edges), whose top eigenvalue is at most `δp`.  That is `c = o(p)` in the
  language of `PaleyLocSecondMomentUnconditional`.
* **Hypothesis B** asks, for every `δ > 0` and all large `p ≡ 1 (mod 4)`, for a Lovász
  certificate `Ȳ` for the **complement** — `1` on the diagonal and on every distinct
  non-adjacent pair, free on the edges — with top eigenvalue at most `(1 + δ)√(p/2)`.

Given both, `ϑ(Ḡ_{p,1}) ∼ √(p/2)`, which is Randomstrasse101 Problem 26.

Neither hypothesis mentions `ϑ`.  Both are statements about explicitly constructible matrices
attached to the arithmetic of `𝔽_p`: the entries of `R` are `|N(u) ∩ N(v)| - d²/m`, which is
one eighth of a Frobenius trace of the Legendre elliptic curve, and `Ȳ` is a dual feasible
point.  So this converts Problem 26 into a construction problem plus a character-sum estimate.

## How the two halves combine

From Hypothesis A, `PaleyLocSecondMomentUnconditional` gives
`ϑ ≤ 2 + √(p/2 + 4δp) = 2 + √(p/2)·√(1 + 8δ)`, so `ϑ/√(p/2) ≤ 2/√(p/2) + √(1 + 8δ)`, which is
below `1 + ε` once `δ ≤ ε/8` and `p > 32/ε²`.

From Hypothesis B, `PaleyLocThetaLowerFromCertificate` gives `ϑ ≥ ((p-1)/2)/θ̄ ≥
((p-1)/2)/((1+δ)√(p/2))`, so `ϑ/√(p/2) ≥ (1 - 1/p)/(1 + δ)`, which is above `1 - ε` once
`δ` and `1/p` are small.  Nothing else is used; in particular no vertex-transitivity, no
orthonormal representations, and no assumption that the limit exists — the two bounds
establish it.

## Term-by-term read-back of the conclusion

`∀ ε > 0, ∃ N, ∀ p, ∀ hp : p.Prime, p % 4 = 1 → N < p →
 |Commons.paleyLocTheta p hp.pos / √((p:ℝ)/2) - 1| < ε`.

This is character-for-character the proposition of this problem's root: ratio form, `N`
outside the `∀ p` so it may not depend on `p`, and `paleyLocTheta` the problem's own quantity.

## What this does not say

It is an implication.  It asserts neither hypothesis, and proves nothing about `ϑ`
unconditionally.  It does not say the hypotheses are necessary — they are sufficient
conditions, and a solver may of course close Problem 26 another way.  Nothing here is about
Schrijver's `ϑ'`, the 2-localization, or prime-power order.  It is not vacuous in the
degenerate sense: each hypothesis is a `∀ δ ∃ N ∀ p ∃ …` statement whose inner existential is
satisfiable for every `p` (take `R` the deviation on the edges and `0` elsewhere, `c` its top
eigenvalue; take `Ȳ` the complement's adjacency-plus-identity, `θ̄` its top eigenvalue) — the
content is entirely in the *size* of `c` and `θ̄`, which is exactly the open part.
-/

namespace Statements.PaleyLocThetaFromCertificates

/-- The canonical proposition: two certificate estimates suffice for Problem 26. -/
abbrev statement : Prop :=
  (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ p : ℕ, ∀ _ : NeZero p, Nat.Prime p → p % 4 = 1 → N < p →
      ∃ (A R : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (c : ℝ),
        (∀ u v, Commons.paleyLocAdj p u v → A u v = 1) ∧
        (∀ u v, ¬ Commons.paleyLocAdj p u v → A u v = 0) ∧
        (∀ u, R u u = 0) ∧
        (∀ u v, Commons.paleyLocAdj p u v →
          R u v = (A * A) u v - (((p : ℝ) - 5) / 4) ^ 2 / (((p : ℝ) - 1) / 2)) ∧
        (c • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - R).PosSemidef ∧
        c ≤ δ * (p : ℝ)) →
  (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ p : ℕ, ∀ _ : NeZero p, Nat.Prime p → p % 4 = 1 → N < p →
      ∃ (Ybar : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (θ : ℝ),
        0 < θ ∧
        (∀ u, Ybar u u = 1) ∧
        (∀ u v, u ≠ v → ¬ Commons.paleyLocAdj p u v → Ybar u v = 1) ∧
        (θ • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - Ybar).PosSemidef ∧
        θ ≤ (1 + δ) * Real.sqrt ((p : ℝ) / 2)) →
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → N < p →
      |Commons.paleyLocTheta p hp.pos / Real.sqrt ((p : ℝ) / 2) - 1| < ε)

/-- The open target. -/
theorem target : statement := sorry

end Statements.PaleyLocThetaFromCertificates
