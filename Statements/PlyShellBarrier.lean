import Mathlib

namespace Statements.PlyShellBarrier

/-- **The min-radius reduction cannot prove `c_d ≤ 2 ^ d`.**

Every known route to Du–McCarty Lemma 5.1 and to Problem 5.2 from above passes through one
reduction: take a ball `B` of minimum radius, rescale to `B(0,1)`, and replace each neighbour
by a unit sub-ball of it whose centre lies in `B(0,2)`. `k`-thinness survives, so the degree
of `B` is at most the value `ρ_d` of the packing problem "how many unit balls with centres in
`B(0,2)`, with no point of `ℝ^d` covered more than `k` times". This statement says that
`ρ_d > 2 ^ d`, strictly, in every dimension `d ≥ 2` — so the reduction, whatever dual
certificate is used with it, can never certify `c_d ≤ 2 ^ d`. Any proof of
`Statements.PlyGridOptimal.statement` must abandon it.

Read-back. `p : Fin m → EuclideanSpace ℝ (Fin d)` with `‖p i‖ ≤ 2` are the `m` centres, in
the closed ball of radius `2`. The middle clause is `k`-thinness of the corresponding unit
balls, written as "no point `y` is within distance `1` of more than `k` centres". The
conclusion `2 ^ d * k < m` is that the configuration is strictly denser than the value `2 ^ d`
that the fine-grid construction attains, so the reduced problem's optimum exceeds `2 ^ d`.

Why it is true. The extremal configuration for the reduced problem is a uniform measure on
the sphere of radius `2`: for a test point at radius `r`, the centres within distance `1` are
those in a cap of half-angle `arccos((3 + r ^ 2)/(4r))`, widest at `r = √3`, where the
half-angle is exactly `π/6`. So the shell's feasible mass is `1/σ_d(π/6)` with `σ_d` the
normalised cap measure, and `1/σ_d(π/6) / 2 ^ d = 1.5, 1.866, 2.168, …, 5.958` at
`d = 2,3,4,…,30`, growing like `(√(6π)/4)√d`. The value `1/σ_d(π/6)` and its asymptotic
`(√(6π)/4) 2 ^ d √d` are classical — they are the naive volume upper bound for the kissing
number, the Chabauty–Shannon–Wyner cap bound specialised at `θ = π/6`; what is new here is
only that this is the exact ceiling of the Lemma 5.1 reduction.

An explicit certificate exists at `d = 2`: `m = 13` equally spaced points on the circle of
radius `2`. Spacing `2π/13 ≈ 0.4833`; a closed arc of angular width `π/3 ≈ 1.0472` holds at
most `3` of them, so `k = 3` is admissible, and `2 ^ 2 * 3 = 12 < 13`. -/
abbrev statement : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∃ (m k : ℕ) (p : Fin m → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖p i‖ ≤ 2) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), {i : Fin m | dist y (p i) ≤ 1}.ncard ≤ k) ∧
      2 ^ d * k < m

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyShellBarrier
