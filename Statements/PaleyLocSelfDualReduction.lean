import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocSelfDualReduction — Conjecture 26 follows from a one-sided bound on both sides

`Commons.paleyLocTheta p` is `ϑ(Ḡ_{p,1})`, the Lovász theta of the complement of the Paley
1-localization.  `coTheta p` below is the *other* theta of the same graph: `ϑ` of the
complement of the complement-adjacency, i.e. `ϑ(G_{p,1})` in Lovász's notation.

Lovász (*On the Shannon capacity of a graph*, 1979, Theorem 8) gives `ϑ(G)ϑ(Ḡ) = n` for every
vertex-transitive `G`, and `G_{p,1}` is vertex-transitive (the multiplicative group of nonzero
squares acts simply transitively on it).  Here `n = (p-1)/2`.

This statement records the consequence, and takes the product identity as an explicit
hypothesis rather than assuming it: **if** the product identity holds, **and** both thetas
admit the one-sided bound `≤ (1+ε)√(p/2)`, **then** Randomstrasse Conjecture 26 holds in the
exact ε-N form of `Statements.PaleyLocTheta`.

The point is that it collapses the two open halves of Conjecture 26 into a single kind of
task.  Unconditionally one knows `ϑ(Ḡ_{p,1}) ≤ (1+o(1))√p` and `ϑ(G_{p,1}) ≤ (1+o(1))√p`,
which are the same elementary fact applied to a graph and to its complement; the product
identity turns each of those into the other's lower bound, which is exactly how the published
window `[½√p, √p]` arises.  Improving *either* upper bound from `√p` to `√(p/2)` gives one
half of the conjecture; improving *both* gives all of it.

Nothing asymptotic is assumed: the hypotheses are the two upper bounds and the algebraic
identity, and the conclusion is the ε-N statement verbatim.
-/

namespace Statements.PaleyLocSelfDualReduction

/-- `ϑ(G_{p,1})`: Lovász's theta of the Paley 1-localization itself, i.e. `thetaClique` of the
complement adjacency.  This is the independence-bounding side. -/
noncomputable def coTheta (p : ℕ) (hp : 0 < p) : ℝ :=
  haveI : NeZero p := NeZero.of_pos hp
  Commons.thetaClique (fun u v : Commons.PaleyLocV p => u ≠ v ∧ ¬ Commons.paleyLocAdj p u v)

/-- The canonical proposition.

If `ϑ(Ḡ_{p,1}) · ϑ(G_{p,1}) = (p-1)/2` for every prime `p ≡ 1 (mod 4)` (Lovász's identity for
vertex-transitive graphs), and if both of those thetas are eventually at most `(1+ε)√(p/2)` for
every `ε > 0`, then `ϑ(Ḡ_{p,1}) ∼ √(p/2)`. -/
abbrev statement : Prop :=
  (∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
      Commons.paleyLocTheta p hp.pos * coTheta p hp.pos = ((p : ℝ) - 1) / 2) →
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → N < p →
      Commons.paleyLocTheta p hp.pos ≤ (1 + ε) * Real.sqrt ((p : ℝ) / 2) ∧
        coTheta p hp.pos ≤ (1 + ε) * Real.sqrt ((p : ℝ) / 2)) →
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → N < p →
      |Commons.paleyLocTheta p hp.pos / Real.sqrt ((p : ℝ) / 2) - 1| < ε)

theorem target : statement := sorry

end Statements.PaleyLocSelfDualReduction
