import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocThetaExceedsSqrtHalf — the clean inequality `ϑ(Ḡ_{p,1}) ≤ √(p/2)` is false

Randomstrasse Conjecture 26 asserts `ϑ(Ḡ_{p,1}) ∼ √(p/2)`.  The obvious strengthening to try
first is the *clean* inequality `ϑ(Ḡ_{p,1}) ≤ √(p/2)` for all `p ≡ 1 (mod 4)`, because it
would give `ω(G_p) ≤ 1 + √(p/2)`, a Hanson–Petridis-strength clique bound by a purely
semidefinite argument, with no error term to chase.

That route is dead: `ϑ(Ḡ_{p,1})` exceeds `√(p/2)` for infinitely many small primes already.
This statement asserts the existence of one such prime.  What survives — the residual — is
the asymptotic form, which is the root statement: nothing here bears on whether
`ϑ/√(p/2) → 1`, only on whether the inequality can be taken in the sharp non-asymptotic
form.
-/

namespace Statements.PaleyLocThetaExceedsSqrtHalf

/-- The canonical proposition: some prime `p ≡ 1 (mod 4)` has `√(p/2) < ϑ(Ḡ_{p,1})`. -/
abbrev statement : Prop :=
  ∃ p : ℕ, ∃ hp : Nat.Prime p, p % 4 = 1 ∧
    Real.sqrt ((p : ℝ) / 2) < Commons.paleyLocTheta p hp.pos

theorem target : statement := sorry

end Statements.PaleyLocThetaExceedsSqrtHalf
