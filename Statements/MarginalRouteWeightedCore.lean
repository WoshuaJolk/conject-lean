import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# MarginalRouteWeightedCore — the one inequality the `k = 2` marginal ceiling rests on

This is the entire non-measure-theoretic content of `MarginalRouteK2Ceiling`, which refutes
`TwinPrimesGEHMarginalRoute` by showing that the `k = 2`, `m = 1` criterion of Polymath8b
Theorem 3.14 has supremum exactly `2`.  That refutation is filed with a complete pen-and-
paper proof and no formalisation.  This statement is the piece of it that can be formalised
today, in one variable, with no Fubini and no product measures: everything else in that proof
is bookkeeping about integrating over two strips of a triangle.

## What is claimed

Write, for `a > 0` and `w` integrable enough on `[0, a]`,

  `A = ∫₀^a w`,   `B = ∫₀^a t·w(t) dt`,   `R = ∫₀^a t·w(t)² dt`.

**(i) A weighted Cauchy–Schwarz.**  `2B²/a² ≤ R`.

**(ii) The core inequality.**  `(2/a)·A·B − A²/2 ≤ R`.

**(iii) Both are sharp, simultaneously, at `w ≡ 1`,** where `R = a²/2` and the left side of
(ii) is also `a²/2`.

## The proofs, which are two completed squares

(i) is `0 ≤ ∫₀^a t·(w(t) − λ)² dt` at `λ = 2B/a²`: expanding gives
`0 ≤ R − 2λB + λ²·a²/2 = R − 4B²/a² + 2B²/a² = R − 2B²/a²`.  The weight `t` inside the
square is what makes `∫₀^a t dt = a²/2` appear and is why the constant is `2/a²`.

(ii) follows from (i) and `2B²/a² − ((2/a)AB − A²/2) = 2(B − aA/2)²/a² ≥ 0`.

That is all.  There is no Hardy inequality here and no fundamental theorem of calculus, and
that is the point: an earlier route to the same ceiling went through
`W(a)² ≤ ∫₀^a t·w² + ∫₀^a W(s)²/s ds` with `W(s) = ∫₀ˢ w`, which needs `W'` a.e. and the
integrability of `W(s)²/s` at `0`.  Replacing the optimal correction term in the ceiling
argument by a **constant** one turns that lemma into (ii), which mentions no antiderivative
at all.  The ceiling is unchanged — still exactly `2`, still attained — because the constant
correction is already optimal at the extremiser, where `w` is constant.

## Where it is used

In `MarginalRouteK2Ceiling`, with `a = 1 − ε`, `w` the restriction to `[0, 1−ε]` of the
`t₁`-marginal of `F`, and `v` likewise for the `t₂`-marginal.  The ceiling argument tests `F`
against
`Θ = w(t₂)1[t₂<a] + v(t₁)1[t₁<a] − (A_v/a)1[t₂>b] − (A_w/a)1[t₁>b]` with `b = 1+ε = 2−a`;
`⟨F,Θ⟩ = J₁ + J₂` because the subtracted terms live exactly where the marginals vanish, and
`‖Θ‖² ≤ 2(J₁+J₂)` reduces, after `2A_vA_w ≤ A_v² + A_w²`, to (ii) applied to `w` and to `v`.
Cauchy–Schwarz then gives `J₁ + J₂ ≤ 2·∫∫F²`, which is the ceiling.

## What is NOT claimed

Nothing about primes, sieves, `H₁`, or the twin prime conjecture.  Nothing about the
two-dimensional variational problem itself — that is `MarginalRouteK2Ceiling`, and it is
still open.  No claim that (i) or (ii) is new; both are elementary, and the only thing here
that is plausibly new is which inequality the `k = 2` ceiling turns out to need.
-/

namespace Statements.MarginalRouteWeightedCore

open MeasureTheory

/-- The canonical proposition: a weighted Cauchy–Schwarz `2B²/a² ≤ R`, the core inequality
`(2/a)AB − A²/2 ≤ R` that the `k = 2` marginal ceiling rests on, and the fact that both are
sharp at `w ≡ 1`. -/
abbrev statement : Prop :=
  (∀ (a : ℝ) (w : ℝ → ℝ), 0 < a →
      IntervalIntegrable w volume 0 a →
      IntervalIntegrable (fun t => t * w t) volume 0 a →
      IntervalIntegrable (fun t => t * w t ^ 2) volume 0 a →
      2 * (∫ t in (0:ℝ)..a, t * w t) ^ 2 / a ^ 2 ≤ ∫ t in (0:ℝ)..a, t * w t ^ 2)
  ∧ (∀ (a : ℝ) (w : ℝ → ℝ), 0 < a →
      IntervalIntegrable w volume 0 a →
      IntervalIntegrable (fun t => t * w t) volume 0 a →
      IntervalIntegrable (fun t => t * w t ^ 2) volume 0 a →
      2 / a * (∫ t in (0:ℝ)..a, w t) * (∫ t in (0:ℝ)..a, t * w t)
          - (∫ t in (0:ℝ)..a, w t) ^ 2 / 2
        ≤ ∫ t in (0:ℝ)..a, t * w t ^ 2)
  ∧ (∀ a : ℝ, 0 < a →
      (∫ t in (0:ℝ)..a, t * (1:ℝ) ^ 2) = a ^ 2 / 2
      ∧ 2 / a * (∫ t in (0:ℝ)..a, (1:ℝ)) * (∫ t in (0:ℝ)..a, t * (1:ℝ))
          - (∫ t in (0:ℝ)..a, (1:ℝ)) ^ 2 / 2 = a ^ 2 / 2)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.MarginalRouteWeightedCore
