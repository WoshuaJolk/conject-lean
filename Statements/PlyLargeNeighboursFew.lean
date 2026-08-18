import Mathlib

namespace Statements.PlyLargeNeighboursFew

/-- **The minimum-radius ball of a `k`-thin family has at most `(2d+1)k` neighbours of radius
`≥ 3d` times its own.**

Du and McCarty (*A survey of degree-boundedness*, European J. Combin. 2024, §5.1) bound the
minimum degree of the intersection graph of a finite `k`-thin collection of balls in `ℝ^d` by
`k · 3 ^ d` (Lemma 5.1), and ask in Problem 5.2 for the optimal constant `c_d`. Every known
route from above passes through their min-radius reduction, whose exact ceiling is the packing
value `ρ_d = Θ(2 ^ d √d)`; `Statements.PlyShellBarrier` records that `ρ_d > 2 ^ d`, so the
reduction can never certify the root `c_d ≤ 2 ^ d`.

This statement is a *structural* constraint on the configurations that make the reduction
tight: **the neighbours of a minimum-radius ball are, on all but `(2d+1)k` of them, of radius
less than `3d` times its own.** So a family in which the minimum-radius ball has degree
exceeding `(2d+1)k` — in particular, any configuration approaching `ρ_d k`, and any
counterexample to the root — has essentially all of that ball's neighbours inside a bounded
band of scales `[r₀, 3d·r₀)`. The "half-space-like" neighbours (balls enormously larger than
`r₀`, externally tangent, which locally look like half-spaces) are few, and cannot carry an
exponential count.

The proof is elementary and uses only `2d + 1` test points. Rescale so the minimum ball is
`B(0,1)`. A neighbour `B(x_i, r_i)` either contains `0`, and at most `k` of those exist by
`k`-thinness at `0`; or `r_i < ‖x_i‖ ≤ r_i + 1`. In the second case pick a coordinate `j` with
`|⟨e_j, x_i⟩| ≥ ‖x_i‖/√d` and the matching sign `σ`, and test at `y = σ·3√d·e_j`. Then
`‖y - x_i‖² = 9d - 2·3√d·|(x_i)_j| + ‖x_i‖²` and, using `‖x_i‖ > r_i` and
`‖x_i‖² - r_i² ≤ (‖x_i‖ - r_i)(‖x_i‖ + r_i) ≤ 1·3r_i`, the inequality `‖y - x_i‖ ≤ r_i`
reduces to exactly `r_i ≥ 3d`. Each of the `2d` test points is inside at most `k` of the balls,
so the second class has at most `2dk` members.

Read-back, term by term.
* `hmin : ∀ i, r i₀ ≤ r i` is what makes `i₀` a ball of minimum radius; the statement says
  nothing about a ball that is not of minimum radius, and it is false without that hypothesis
  (a large ball can have many far larger neighbours).
* `k`-thin is the source's own definition, "every point of the ground set is in at most `k`
  elements", read on `ℝ^d`, with `Set.ncard` on subsets of `Fin n`.
* Adjacency is the set-level condition `(closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty`,
  the problem's own spelling.
* The threshold `3 * (d:ℝ) * r i₀` and the bound `(2d+1)k` are both explicit; no `O`-notation
  and no additive slack.
* The conclusion is not vacuous: at `d = 1`, `n = 2`, `x = ![0, 3]`, `r = ![1, 3]`, `k = 2`,
  the two balls meet, the second has radius `3 = 3·1·1`, and the counted set is `{1}`.

This is a lemma about the reduction, not a bound on `c_d`; it moves no endpoint of the
problem's progress chart, and it should not be read as doing so. -/
abbrev statement : Prop :=
  ∀ (d n k : ℕ), 1 ≤ d →
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
      (∀ i, 0 < r i) →
      (∀ p : EuclideanSpace ℝ (Fin d),
          {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
      ∀ i₀ : Fin n, (∀ i, r i₀ ≤ r i) →
        {i : Fin n | i ≠ i₀ ∧
            (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty ∧
            3 * (d : ℝ) * r i₀ ≤ r i}.ncard
          ≤ (2 * d + 1) * k

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyLargeNeighboursFew
