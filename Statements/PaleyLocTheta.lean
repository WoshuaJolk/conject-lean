import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocTheta — is the Lovász theta of the Paley 1-localization asymptotic to `√(p/2)`?

This module is the **single source of truth** for what this problem means.  The verifier
reads `Statements.PaleyLocTheta.statement` and nothing else.

## The informal statement, and the term-by-term read-back

Bandeira–Dmitriev, *Randomstrasse101: Open Problems of 2025* (arXiv:2603.29571), Problem 26,
and the companion post <https://randomstrasse101.math.ethz.ch/posts/PaleyGraph/>:

> **Problem 26.** `ϑ(Ḡ_{p,1}) ∼ √(p/2)` (for `p ≡ 1 (mod 4)` prime), where `G_{p,1}` is the
> 1-localization of the Paley graph — the induced subgraph on the vertices adjacent to `0`.

Read back against the Lean below, term by term:

* "`p ≡ 1 (mod 4)` prime" → `∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → …`.  Both hypotheses
  are quantified over, neither is folded into a definition.  They are satisfiable —
  `p = 5, 13, 17, 29, …` — so the statement is not vacuous; by Dirichlet there are
  infinitely many, so the tail quantifier `N < p` does not empty it either.
* "`Ḡ_{p,1}`", the complement of the 1-localization → `Commons.paleyLocTheta`, which is
  `Commons.thetaClique (Commons.paleyLocAdj p)`, whose semidefinite program puts its zero
  pattern on the **non-adjacent** distinct pairs of `paleyLocAdj`.  That is `ϑ` of the
  complement, the quantity that upper-bounds the *clique* number, which is the quantity
  Problem 26 is about (it is introduced there precisely as a bound on `ω(G_p)`).
* "`∼`", asymptotic equivalence as `p → ∞` along the primes `≡ 1 (mod 4)` → the explicit
  `∀ ε > 0, ∃ N, ∀ p > N, |ϑ / √(p/2) - 1| < ε`.  Ratio form, not difference form, which is
  what `∼` means.  The `∃ N` is outside the `∀ p`, so `N` may not depend on `p`.
* "`√(p/2)`" → `Real.sqrt ((p : ℝ) / 2)`, the cast of `p` divided by `2` inside the root.

## What a solution has to do

Nothing here is folded in.  What is provable today by standard tools is strictly weaker:
the Hoffman ratio bound together with Lovász's `ϑ(G)ϑ(Ḡ) = n` for vertex-transitive `G`
pins the ratio `ϑ(Ḡ_{p,1})/√p` into `[1/2 - o(1), 1 + o(1)]`, and Problem 26 asserts the
value `1/√2`, the geometric mean of those two ends.  Either half of the asymptotic —
`limsup ≤ 1/√2` or `liminf ≥ 1/√2` — is open, and neither is assumed below.  A refutation
is a first-class outcome: nobody has proved the limit exists.
-/

namespace Statements.PaleyLocTheta

/-- The canonical proposition.  This is the type the verifier demands.

Along the primes `p ≡ 1 (mod 4)`, the Lovász theta function of the complement of the
Paley 1-localization is asymptotically `√(p/2)`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → N < p →
    |Commons.paleyLocTheta p hp.pos / Real.sqrt ((p : ℝ) / 2) - 1| < ε

/-- The open target.  Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PaleyLocTheta
