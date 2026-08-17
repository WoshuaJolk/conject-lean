import Mathlib

namespace Statements.PlyLowerHalfGrid

/-- **`c_d ≥ 2 ^ (d-1)` in Du–McCarty Problem 5.2: `c_d` is exponential in `d`.**

Du and McCarty write, immediately after Problem 5.2: "We suspect that `c_d` must be
exponential in `d`; perhaps this can be shown by including points of a very fine grid
independently at random with an appropriately chosen probability." Nothing in the literature
proves it. This statement is the de-randomised form of that suspicion, and it is sharp for
the construction: a fine lattice of unit balls filling a large ball `B(0,R)` is `k`-thin with
`k ≈ ρ v_d`, and *every* member — including the ones on the boundary sphere, which see only a
half-space's worth of neighbours — has degree at least `(2 ^ (d-1) - o(1)) k`.

Read-back. Saying `c_d ≥ 2 ^ (d-1)` is saying that no integer `c` with `2 * c < 2 ^ d` is
admissible, for any additive constant `C` whatsoever. So: given `d ≥ 1`, given such a `c`, and
given `C`, there is a finite `k`-thin collection of balls of positive radius in `ℝ^d` in which
**every** member has intersection-graph degree strictly greater than `c * k + C`. The
quantifier order matters: `c` and `C` come first, the family is built against them. `2 * c <
2 ^ d` is `c < 2 ^ (d-1)` written without truncated subtraction.

This is one half of the campaign bracket `2 ^ (d-1) ≤ c_d ≤ Θ(2 ^ d √d)`; the other half is
`Statements.PlyUpperTwoPowSqrt`. Together with Du–McCarty's Lemma 5.1 (`c_d ≤ 3 ^ d`) it
gives the exponential rate of `c_d` a proved lower bound of `2` for the first time. -/
abbrev statement : Prop :=
  ∀ (d c C : ℕ), 1 ≤ d → 2 * c < 2 ^ d →
    ∃ (k n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
      0 < n ∧
      (∀ i, 0 < r i) ∧
      Function.Injective (fun i => (x i, r i)) ∧
      (∀ p : EuclideanSpace ℝ (Fin d),
          {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) ∧
      ∀ i₀ : Fin n,
        c * k + C <
          {i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyLowerHalfGrid
