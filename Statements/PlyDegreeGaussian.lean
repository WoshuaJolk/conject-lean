import Mathlib

open MeasureTheory Real Metric Set

namespace Statements.PlyDegreeGaussian

/-- **A machine-checked upper bound on the degree in Du–McCarty Problem 5.2.**

Du and McCarty (*A survey of degree-boundedness*, EJC 2024) prove in Lemma 5.1 that a finite
`k`-thin collection of balls in `ℝ^d` has a ball of degree less than `k · 3 ^ d`, and ask in
Problem 5.2 for the optimal constant `c_d`. This statement is the same conclusion with the
constant produced by a Gaussian test function instead of a volume comparison, for every
`lam > 0` at once.

It is the composition of two things: Du–McCarty's own min-radius reduction — take a ball of
minimum radius, replace each neighbour by a sub-ball of that radius contained in it, whose
centre then lies within twice the radius — and a Gaussian dual bound for the resulting packing
that uses the reflection symmetry of the ball, so that `‖p + u‖² ≤ 5 + 2⟪p,u⟫` replaces the
crude `‖p + u‖² ≤ 9`.

Specialising `lam = d/10` and `volume (closedBall 0 1) = √π ^ d / Γ(d/2+1)` turns the
conclusion into `degree ≤ k · Γ(d/2+1) · (10e/d)^(d/2)`, which by Stirling is
`(1 + o(1)) · √(πd) · (√5)^d · k`. Since `√5 = 2.236… < 3` this improves the constant of
Lemma 5.1 for every large `d`, and it is the first improvement on that `3 ^ d`.

Read-back. `x` and `r` are the centres and radii of `n` closed balls of positive radius; no
injectivity is assumed, so multisets of balls are covered too. `k`-thin is Du–McCarty's own
definition read on `ℝ^d`. The set whose `ncard` is bounded is the neighbourhood of `i₀` in the
intersection graph `G(B)` of Lemma 5.1: the balls other than `i₀` that meet `i₀`. The bound is
stated multiplicatively rather than as a quotient so that no positivity side condition enters
the statement. -/
abbrev statement : Prop :=
  ∀ (d : ℕ) (lam : ℝ), 0 < lam → ∀ (n k : ℕ), 0 < n →
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ), (∀ i, 0 < r i) →
      (∀ p : EuclideanSpace ℝ (Fin d),
          {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
      ∃ i₀ : Fin n,
        ({i : Fin n | i ≠ i₀ ∧
            (Metric.closedBall (x i) (r i) ∩
              Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard : ℝ)
          * (Real.exp (-5 * lam) *
              (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
        ≤ k * (Real.pi / lam) ^ ((d : ℝ) / 2)

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyDegreeGaussian
