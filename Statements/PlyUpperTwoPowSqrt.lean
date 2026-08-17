import Mathlib

namespace Statements.PlyUpperTwoPowSqrt

/-- **`c_d = O(2 ^ d √d)` in Du–McCarty Problem 5.2: the `3 ^ d` of Lemma 5.1 improves.**

Du–McCarty's Lemma 5.1 gives `c_d ≤ 3 ^ d`, by the volume argument "a neighbour of the
minimum-radius ball `B` occupies at least a `3 ^ (-d)` fraction of the dilate `3B`". This
statement is the assertion that the constant may be taken `K * 2 ^ d * √d` instead — an
improvement by a factor `(3/2) ^ d / √d`, from `59 049` to `≈ 3 914` at `d = 10` and from
`2.06 × 10 ^ 14` to `≈ 6.7 × 10 ^ 9` at `d = 30`.

Route, for a prospective prover. Rescale so the minimum-radius ball is `B(0,1)`; replace each
neighbour by a unit sub-ball of it with centre in `B(0,2)`, which preserves `k`-thinness; the
resulting count is at most the value `ρ_d` of the linear program "maximum mass of a measure
supported in `B(0,2)` whose unit-ball counting function is everywhere `≤ 1`". Any `f ≥ 0`
gives `ρ_d ≤ (∫ f) / min_{|c| ≤ 2} (f * 1_{B(0,1)})(c)`; `f = 1_{B(0,R)}` gives
`ρ_d ≤ R ^ d / λ_d(R)` where `λ_d(R)` is the fraction of a unit ball centred at distance `2`
from the origin lying inside `B(0,R)`. `R = 3` recovers `3 ^ d` exactly. Writing
`a = (5 - R ^ 2)/4`, the exponential rate of `R ^ d / λ_d(R)` is `R / √(1 - a ^ 2)`, whose
square is `16 R ^ 2 / (-(R ^ 2 - 1)(R ^ 2 - 9))`; this is minimised at `R ^ 2 = 3` with value
exactly `4`. So `R = √3` gives rate exactly `2`, and the surviving `√d` is the reciprocal of
the Gaussian tail factor at `a = 1/2`.

Honesty note. Report 50 of the campaign asserted `ρ_d = Θ(2 ^ d √d)` from a numerical table
of `min_R R ^ d / λ_d(R)` for `d ≤ 30`, not from a proof; report 50b flagged exactly this.
The closed-form optimisation above, which supplies the missing asymptotic argument, was done
in the posing session and has not been machine-checked. This statement is therefore filed as
a claim awaiting a verified artifact, and the problem's progress chart does **not** record its
bound. -/
abbrev statement : Prop :=
  ∃ K : ℝ,
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℕ,
      ∀ (k n : ℕ), 0 < n →
        ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
          (∀ i, 0 < r i) →
          Function.Injective (fun i => (x i, r i)) →
          (∀ p : EuclideanSpace ℝ (Fin d),
              {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
          ∃ i₀ : Fin n,
            ({i : Fin n | i ≠ i₀ ∧
                (Metric.closedBall (x i) (r i) ∩
                  Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard : ℝ)
              ≤ K * 2 ^ d * Real.sqrt d * k + C

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyUpperTwoPowSqrt
