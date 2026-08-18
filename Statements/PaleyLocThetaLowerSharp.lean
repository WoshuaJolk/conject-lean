import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocThetaLowerSharp — the sharp elementary lower bound on `ϑ(Ḡ_{p,1})`

For every prime `p ≡ 1 (mod 4)`,

`(√p - 1 + (p-1)/2) / (√p + 1) ≤ ϑ(Ḡ_{p,1})`.

This is `√p/2 + 1/2 - O(1/√p)`, so it improves the published lower bound
`√p/2 - 1/(2√p)` (Wang–Shen–Kobzar, eq. (60), obtained by Feige–Krauthgamer pseudomoments)
by an additive `1 + o(1)`, and it improves the cruder `(p-1)/(2(√p+1))` of
`Statements.PaleyLocThetaWindow` by `(√p-1)/(√p+1) → 1`.

The constant in front of `√p` is still `1/2`: this does **not** move the answer space, and it
is not claimed to.  What it does is make the elementary construction exact.  The certificate
is the same one: `X = c(√p·I + H|_Q + J|_Q)` with `c = 1/(|Q|(√p+1))`, whose zero pattern is
exactly the non-edges because `χ(u-v) = -1` there.  The only slack in the earlier version was
the estimate `1ᵀH|_Q1 ≥ -√p·|Q|`, and the exact value is `1ᵀH|_Q1 = ∑_{u,v ∈ Q} χ(u-v) =
-(p-1)/2`, evaluated by expanding the indicator of the nonzero squares as `(χ² + χ)/2` and
reducing to `∑ₓ χ(x) = 0`, `χ(-1) = 1` and the Jacobi sum `∑ₛ χ(s)χ(1-s) = -1`.  That is the
same evaluation behind `Statements.PaleyLocRegular`.
-/

namespace Statements.PaleyLocThetaLowerSharp

/-- The canonical proposition: the sharp elementary lower bound. -/
abbrev statement : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
    (Real.sqrt p - 1 + ((p : ℝ) - 1) / 2) / (Real.sqrt p + 1)
      ≤ Commons.paleyLocTheta p hp.pos

theorem target : statement := sorry

end Statements.PaleyLocThetaLowerSharp
