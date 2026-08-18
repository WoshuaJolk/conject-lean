import Mathlib

namespace Statements.PlyNearTangency

/-- **In the reduced packing problem behind Du–McCarty Lemma 5.1, the centres away from the
boundary sphere are exponentially few: a `(1 + η/2)^((d-1)/2)` factor is gained at depth `η`.**

Du and McCarty (*A survey of degree-boundedness*, European J. Combin. 2024, §5.1) reduce the
minimum degree of a `k`-thin collection of balls in `ℝ^d` to the packing count "how many unit
balls can have centres in `B(0,2)` with no point of `ℝ^d` covered more than `k` times". That
count is `ρ_d = Θ(2^d √d) · k`, and `Statements.PlyUpperTwoPowSqrt` is the matching degree
bound. This statement refines the count by **depth**: for every `η ∈ [0, 1/2]`, the centres at
distance at most `2 - η` from the origin number at most

`K · 2^d · √d · k / (1 + η/2)^((d-1)/2)`.

Reading it. At `η = 0` it is the packing bound itself. For `η` a constant, the right-hand side
is exponentially smaller than `2^d k`, so a configuration of size `≥ 2^d k` — which is what any
counterexample to this problem's root `Statements.PlyGridOptimal` must produce at the
minimum-radius ball — has essentially all of its centres within `O(log d / d)` of the boundary
sphere `‖p‖ = 2`. Undoing the reduction: **the neighbours of the minimum-radius ball in any
would-be counterexample are, on all but an exponentially small fraction, within `O(log d / d)`
of external tangency with it.** Together with `Statements.PlyLargeNeighboursFew`, which says
all but `(2d+1)k` of those neighbours have radius less than `3d` times the minimum, this pins
the shape of any extremal configuration: near-tangent, and of comparable radius. It is the
sphere-shell picture, proved.

The proof is the `√3` dual of `Statements.PlyUpperTwoPowSqrt` run at a general cap level. For
`‖p‖ ≤ 2 - η` set `τ = (2 - (2-η)^2)/(2(2-η)) ≤ 0`; then `s^2 + 2sτ ≤ 2` for every
`s ∈ [0, 2-η]`, since `s^2 + 2sτ - 2 = (s - (2-η))(s + 2/(2-η))`, so the cap
`{w : ‖w‖ ≤ 1, ⟪u,w⟫ ≤ τ}` translated to `p` lies inside `B(p,1) ∩ B(0,√3)`. A cylinder of
height `h` and radius `β` with `β^2 = 1 - (h - τ)^2` sits inside that cap and has volume
`h · β^(d-1) · v_(d-1)`; the gain over the `τ = -1/2` case is
`1 - τ^2 ≥ (3/4)(1 + η/2)`, which is
`(2 - S)(2S^3 + S^2 - 2S - 4) ≥ 0` for `S = 2 - η ∈ [3/2, 2]`. Finally
`v_(d-1)/v_d ≥ √(d/(2π))` by log-convexity of `Γ`, and the `Θ(√d)` and the `2^d` come out as
in the unrefined bound.

Read-back, term by term.
* `d ≥ 2`, because the argument splits off one coordinate and needs `d - 1 ≥ 1`.
* `η ∈ [0, 1/2]`, so `2 - η ∈ [3/2, 2]`; outside that range `1 - τ^2 ≥ (3/4)(1+η/2)` fails and
  the statement is not asserted.
* No hypothesis `‖p j‖ ≤ 2` is needed: only the centres with `‖p j‖ ≤ 2 - η` are counted.
* `k`-thin is written as Du–McCarty write it, "no point is within distance `1` of more than
  `k` centres", with `Set.ncard` on subsets of `Fin N`.
* The `√((1 + η/2)^(d-1))` on the left rather than a division on the right keeps the statement
  free of `rpow` and of any positivity side condition.
* Non-vacuous: `d = 2`, `η = 0`, `N = 1`, `k = 1`, `p 0 = 0` satisfies the hypotheses with the
  counted set non-empty.

This is a lemma about the reduced packing problem, not a bound on `c_d`; it moves no endpoint
of the problem's progress chart. -/
abbrev statement : Prop :=
  ∃ K : ℝ,
    ∀ (d : ℕ), 2 ≤ d → ∀ (η : ℝ), 0 ≤ η → η ≤ 1/2 →
      ∀ (N k : ℕ) (p : Fin N → EuclideanSpace ℝ (Fin d)),
        (∀ y : EuclideanSpace ℝ (Fin d), {j : Fin N | dist y (p j) ≤ 1}.ncard ≤ k) →
        ({j : Fin N | ‖p j‖ ≤ 2 - η}.ncard : ℝ) * Real.sqrt ((1 + η/2)^(d-1))
          ≤ K * 2 ^ d * Real.sqrt d * k

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyNearTangency
