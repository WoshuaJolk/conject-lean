import Mathlib

open MeasureTheory Real Metric Set

namespace Statements.PlyGaussianDual

/-- **A Gaussian dual bound for the reduced problem behind Du–McCarty Lemma 5.1, sharpened by
reflection.**

Lemma 5.1 of Du and McCarty (*A survey of degree-boundedness*, EJC 2024, §5.1) bounds the
minimum degree of the intersection graph of a `k`-thin family of balls in `ℝ^d` by `k · 3^d`.
Its proof reduces, via the ball of minimum radius, to this packing question: how many unit
balls can have their centres in the closed ball of radius `2` while no point of `ℝ^d` is
covered more than `k` times? Their answer is `k · 3^d`, obtained by comparing volumes inside
the ball of radius `3`.

This statement replaces that volume comparison by a Gaussian test function `exp (-lam ‖y‖²)`
together with the reflection symmetry of the unit ball. For a centre `p` with `‖p‖ ≤ 2` and
`‖u‖ ≤ 1`, `‖p + u‖² = ‖p‖² + 2⟪p,u⟫ + ‖u‖² ≤ 5 + 2⟪p,u⟫`, and the term `2⟪p,u⟫` integrates
away over the unit ball because `exp(a) + exp(-a) ≥ 2`. That is the whole content: the crude
argument must use `‖p + u‖² ≤ 9`, and `5` in place of `9` is exactly what separates the
published `3^d` from the rate below.

What it gives. Taking `lam = d/10` and `volume (closedBall 0 1) = √π^d / Γ(d/2+1)` in
dimension `d`, the conclusion reads `N ≤ k · Γ(d/2+1) · (10e/d)^(d/2)`, which by Stirling is
`(1 + o(1)) · √(πd) · (√5)^d · k`. Since `√5 = 2.236… < 3`, this is an improvement on the
constant of Lemma 5.1 for all large `d`; the exponential rate `√5` is also the exact ceiling
of this family of arguments, because a dual that uses only the reflection symmetry of the ball
and not a cap-volume estimate cannot do better.

The statement is left in the raw form actually proved — quantified over `lam`, with the volume
of the unit ball appearing as it stands — because that is the honest content and every
specialisation, including the Stirling step, follows from it by arithmetic. -/
abbrev statement : Prop :=
  ∀ (d : ℕ) (lam : ℝ), 0 < lam →
    ∀ (N k : ℕ) (p : Fin N → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖p i‖ ≤ 2) →
      (∀ y : EuclideanSpace ℝ (Fin d), {i : Fin N | dist y (p i) ≤ 1}.ncard ≤ k) →
      (N : ℝ) * (Real.exp (-5 * lam) *
          (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
        ≤ k * (Real.pi / lam) ^ ((d : ℝ) / 2)

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyGaussianDual
