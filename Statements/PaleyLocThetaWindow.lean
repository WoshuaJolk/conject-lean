import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocThetaWindow — explicit, self-contained bounds on `ϑ(Ḡ_{p,1})`

Two explicit non-asymptotic inequalities on `Commons.paleyLocTheta p`, valid for every prime
`p ≡ 1 (mod 4)`:

* `(p-1)/(2(√p+1)) ≤ ϑ(Ḡ_{p,1})`, which is `(1/2 - o(1))√p`;
* `ϑ(Ḡ_{p,1}) ≤ 1 + √p`, which is `(1 + o(1))√p`.

In the normalised unit `c = lim ϑ/√p` of the problem these are `c ≥ 1/2` and `c ≤ 1`: they pin
the same window that the literature already records, and they do **not** move it.  What they add
is that both ends now rest on a single elementary certificate rather than on two different
citations: the Paley conference matrix `H` on `ZMod p`, `H a b = χ(a-b)` for `χ` the quadratic
character, satisfies `H² = p·I - J`, and therefore `√p·I ± H` is positive semidefinite (its
square is `2√p(√p·I ± H) - J`, a sum of a Gram matrix and `J`).  Compressing that to the
nonzero squares gives:

* the dual certificate `A = I + H|_Q`, which is `1` on the diagonal and on the edges of
  `G_{p,1}`, with `(1+√p)I - A = √p·I - H|_Q` positive semidefinite — hence `ϑ ≤ 1 + √p`;
* the primal certificate `X = c(√p·I + H|_Q + J|_Q)`, whose zero pattern is exactly the
  non-edges of `G_{p,1}` because `χ(u-v) = -1` there — hence the lower bound.

The vertex count `(p-1)/2` used in the lower bound is itself derived from `∑_a χ(a) = 0`.

Both halves of Randomstrasse Conjecture 26 lie strictly inside this window: the conjecture says
`c = 1/√2`, and closing either end to `1/√2` is open.
-/

namespace Statements.PaleyLocThetaWindow

/-- The canonical proposition: the explicit two-sided window on `ϑ(Ḡ_{p,1})`. -/
abbrev statement : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
    ((p : ℝ) - 1) / (2 * (Real.sqrt p + 1)) ≤ Commons.paleyLocTheta p hp.pos ∧
      Commons.paleyLocTheta p hp.pos ≤ 1 + Real.sqrt p

theorem target : statement := sorry

end Statements.PaleyLocThetaWindow
