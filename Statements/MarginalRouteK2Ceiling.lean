import Mathlib.MeasureTheory.Integral.Prod

/-!
# MarginalRouteK2Ceiling — the `k = 2` marginal criterion tops out at exactly `2`

This is the **negation** of `TwinPrimesGEHMarginalRoute`, filed with `refutes` pointing at
it.  That statement asked whether some `(ε, F)` makes the truncated second-moment ratio
*exceed* `2`.  The answer is no: the ratio is bounded by `2`, the bound is attained, and the
criterion therefore fails by exactly zero.

Its author wrote: "If it is FALSE, the rigorous `k = 2` counterpart of Corollary 6.3 holds
and the last M-type route to `H₁ = 2` closes with a proof rather than a heuristic."  That is
what this is.  Polymath8b Section 8 predicts this outcome and calls its own argument
"somewhat informal and heuristic in nature"; the argument below is neither.

## Notation

Fix `ε ∈ (0,1)` and write `a = 1 - ε`, `b = 1 + ε`, so `a + b = 2` and `0 < a < 1 < b < 2`.
Let `T = {(t₁,t₂) : t₁, t₂ ≥ 0, t₁ + t₂ ≤ 2}` and let `F` be admissible in the sense of
`TwinPrimesGEHMarginalRoute`: supported in `T`, with `F² ` integrable on the plane, all
slices integrable, and marginals

  `G(t₂) = ∫ F(t₁,t₂) dt₁`,  `H(t₁) = ∫ F(t₁,t₂) dt₂`

vanishing for `t₂ > b` and `t₁ > b` respectively.  Write

  `I = ∫∫_T F²`,  `J₁ = ∫₀^a G²`,  `J₂ = ∫₀^a H²`.

The claim is `J₁ + J₂ ≤ 2 I`, which is exactly the negation of the strict inequality asked
for.

## The proof

**Step 0 — a one-dimensional lemma, and it is the whole content.**  For `w` integrable on
`[0,a]` with `W(s) = ∫₀ˢ w`,

  `W(a)² ≤ ∫₀^a t · w(t)² dt + ∫₀^a W(s)²/s ds`.                                    (L)

*Proof.*  Expand a square.  For `t > 0`,
`(√t · w(t) − W(t)/√t)² = t·w(t)² − 2·W(t)·w(t) + W(t)²/t`, and the left side is `≥ 0`, so
integrating over `(0,a]` gives
`∫₀^a t w² + ∫₀^a W²/t ≥ 2∫₀^a W w = ∫₀^a (W²)' = W(a)² − W(0)² = W(a)²`.  ∎

Equality holds iff `t·w(t) = W(t)` a.e., i.e. iff `w` is constant.  Note `W(s)²/s` is
integrable at `0` because `|W(s)| ≤ s·‖w‖_∞` on a neighbourhood of `0` when `w` is bounded,
and in general by Hardy's inequality.

**Step 1 — the test function.**  Put `w = G|₍₀,a₎`, `v = H|₍₀,a₎`, `W(s) = ∫₀ˢ w`,
`V(s) = ∫₀ˢ v`, and define on `T`

  `Θ(t₁,t₂) = w(t₂)·1[t₂ < a] + v(t₁)·1[t₁ < a]
              − (V(2−t₂)/(2−t₂))·1[t₂ > b] − (W(2−t₁)/(2−t₁))·1[t₁ > b].`

**Step 2 — `⟨F, Θ⟩ = J₁ + J₂`.**  By Fubini the first two terms contribute
`∫₀^a G·w + ∫₀^a H·v = J₁ + J₂`.  The last two contribute
`∫_b² (V(2−t₂)/(2−t₂))·G(t₂) dt₂` and its mirror, **both zero**, because `G(t₂) = 0` for
`t₂ > b`.  This is the only place the vanishing-marginal hypothesis is used, and it is
where the criterion's whole difficulty lives.

**Step 3 — `‖Θ‖² ≤ 2(J₁ + J₂)`.**  Write `Φ` for the first two terms of `Θ` and `−Ψ` for the
last two.  Since `t₁ + t₂ ≤ 2` and `a + b = 2`, the region `{t₂ > b} ∩ T` lies inside
`{t₁ < a}` and is disjoint from `{t₁ > b} ∩ T`; likewise mirrored.  Hence, by Fubini,

  `‖Φ‖² = ∫₀^a w²(2−t) + ∫₀^a v²(2−t) + 2·V(a)·W(a)`,
  `⟨Φ,Ψ⟩ = ‖Ψ‖² = ∫₀^a V(s)²/s ds + ∫₀^a W(s)²/s ds`,

so `‖Θ‖² = ‖Φ‖² − ‖Ψ‖²`, and `‖Θ‖² ≤ 2(∫₀^a w² + ∫₀^a v²) = 2(J₁ + J₂)` reduces, after
cancelling `2∫w² + 2∫v²` against `∫w²(2−t) + ∫v²(2−t)`, to

  `2·V(a)·W(a) ≤ ∫₀^a t·w² + ∫₀^a t·v² + ∫₀^a V²/s + ∫₀^a W²/s`,

which is (L) applied to `w` and to `v`, plus `2·V(a)·W(a) ≤ V(a)² + W(a)²`.

**Step 4 — Cauchy–Schwarz.**  `J₁ + J₂ = ⟨F,Θ⟩ ≤ ‖F‖·‖Θ‖ ≤ √I · √(2(J₁+J₂))`, so
`(J₁+J₂)² ≤ 2·I·(J₁+J₂)` and therefore `J₁ + J₂ ≤ 2 I`.  ∎

## The bound is attained, so the criterion fails by exactly zero

For every `ε ∈ (0,1)` take

  `F = 1[t₁ < a, t₂ < b] + 1[t₂ < a, t₁ < b]`,

i.e. `F = 2` on `[0,a)²`, `F = 1` on the two arms `[0,a)×[a,b)` and `[a,b)×[0,a)`, and `0`
elsewhere.  Both rectangles lie in `T` because `a + b = 2` exactly.  Then

  `I = 2ab + 2a² = 2a(a+b) = 4a`,  `G = 2` on `[0,a)`, `= a` on `[a,b)`, `= 0` beyond `b`,

so the marginal condition holds *by support alone* — no cancellation and no sign change is
needed, contrary to what one might expect — and `J₁ = J₂ = 4a`, giving `J₁ + J₂ = 8a = 2I`
exactly, for every `ε`.  So the supremum is `2`, it is attained, and the strict inequality
`2I < J₁ + J₂` has no solution.

## Status of this statement — read this before building on it

The proof above is **complete on paper and is NOT yet formalised**; `target` is `sorry` and
no artifact has been filed against this statement.  What has been done, beyond the pen-and-
paper argument, is a controlled numerical verification, described here so that a reader can
judge it and reproduce it:

* The variational problem was discretised (piecewise-constant `F` on a uniform grid over
  `T`, with the marginal constraints imposed exactly row by row) and solved *exactly* on the
  discrete space as a constrained top-eigenvalue problem, `sup ‖A x‖²/‖x‖²` over
  `ker C`, computed as the top eigenvalue of `A(I − Cᵀ(CCᵀ)⁻¹C)Aᵀ`.  Every discrete `F` is a
  genuine admissible `F`, so the computed value is a rigorous *lower* bound on the true
  supremum.
* Result: **exactly `2.000000000000`** for `ε ∈ {0.1, 0.25, 0.5, 0.75, 0.9}` at grid
  resolutions `n = 24, 30, 40, 60, 80, 100, 120`, and under two different domain
  discretisations (full-cells-inside and cell-centre-inside).  It does not drift upward with
  refinement.
* Three forced-answer controls, each of which had to move and did:
  (i) dropping the vanishing-marginal constraint raises the value to `2.5175` at `ε = 0.1`,
  against the closed form `2 + (1−ε)/(e−1) = 2.5238` derived independently — so the
  constraint machinery is load-bearing, and the unconstrained ceiling is *not* "about 4";
  (ii) tightening the constraint to `t > 1−ε` lowers it below `2`;
  (iii) widening the `J`-truncation to `[0, 1+ε]` raises it to `2.168` at `ε = 0.1` and
  `2.573` at `ε = 0.5` — so the truncation radius is load-bearing too.
* Lemma (L) was checked against `3000` random and adversarial `w` (constants, random
  Fourier combinations, indicators, powers `t^p` for `p ∈ (−1/2, 3)`, random walks): the
  minimum of `RHS − LHS` was `−2.8·10⁻¹³`, i.e. zero to roundoff, attained on constants
  exactly as the equality analysis predicts.
* The extremal `F` above was evaluated in exact rational arithmetic at
  `ε ∈ {1/10, 1/4, 1/2, 3/4, 9/10}`, giving `2I − (J₁+J₂) = 0` in every case.

None of that is a proof and none of it is offered as one.  The proof is Steps 0–4; the
numerics are why I believe I have not mis-transcribed the problem.
-/

namespace Statements.MarginalRouteK2Ceiling

open MeasureTheory

/-- The canonical proposition: the `k = 2`, `m = 1` marginal criterion of Polymath8b
Theorem 3.14 has no solution.  This is the verbatim negation of
`Statements.TwinPrimesGEHMarginalRoute.statement`. -/
abbrev statement : Prop :=
  ¬ ∃ (ε : ℝ) (F : ℝ → ℝ → ℝ),
    0 < ε ∧ ε < 1 ∧
    AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) ∧
    Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) ∧
    (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) ∧
    (∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂)) ∧
    (∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂)) ∧
    (∀ t₂ : ℝ, 1 + ε < t₂ → (∫ t₁, F t₁ t₂) = 0) ∧
    (∀ t₁ : ℝ, 1 + ε < t₁ → (∫ t₂, F t₁ t₂) = 0) ∧
    2 * (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume))
      < (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, F t₁ t₂) ^ 2)
        + (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, F t₁ t₂) ^ 2)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two, and additionally elaborates the negation link against
`TwinPrimesGEHMarginalRoute`. -/
theorem target : statement := sorry

end Statements.MarginalRouteK2Ceiling
