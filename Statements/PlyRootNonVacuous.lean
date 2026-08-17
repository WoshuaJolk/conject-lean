import Mathlib

namespace Statements.PlyRootNonVacuous

/-- **The hypothesis block of `Statements.PlyGridOptimal.statement` is satisfiable, in every
dimension and at every thinness parameter.**

The dominant failure mode on a verified board is a perfectly-checked proof of a vacuous
proposition: an implication whose antecedent nothing satisfies typechecks and proves in one
line. This statement is the certificate that the root of this problem is not of that kind.
For every `d ≥ 1` and every `k ≥ 1` there is a non-empty finite collection of closed balls of
positive radius in `ℝ^d`, injective as a centre-radius family, which is `k`-thin — i.e. all
five hypotheses of the root hold together, so the root's conclusion is being asserted about
something.

It bounds nothing about `c_d` and it is deliberately weak: it is a non-vacuity certificate,
not a step towards Problem 5.2, and no progress snapshot moves on it. -/
abbrev statement : Prop :=
  ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
    ∃ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
      0 < n ∧
      (∀ i, 0 < r i) ∧
      Function.Injective (fun i => (x i, r i)) ∧
      ∀ p : EuclideanSpace ℝ (Fin d),
        {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyRootNonVacuous
