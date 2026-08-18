import Mathlib.MeasureTheory.Integral.Prod

/-!
# TwinPrimesGEHMarginalSharp — the k = 2 marginal route sits exactly on the threshold

Companion to `TwinPrimesGEHMarginalRoute`, which asks whether Polymath8b (arXiv:1407.4897)
Theorem 3.14 at `k = 2` can ever fire: is there a square-integrable `F` on `2·R₂` with
vanishing marginals beyond `1 + ε` whose truncated second-moment ratio exceeds `2`?

This statement settles the **other side** of that question, unconditionally: for every
`ε ∈ (0,1)` and every `c < 2` such an `F` exists with ratio exceeding `c`.

So the supremum of the `k = 2` Theorem-3.14 functional is **at least 2**, for every `ε`.
Combined with the criterion's own requirement — Theorem 3.14 needs the ratio to exceed
`2m/θ`, and `0 < θ < 1`, `m ≥ 1` force `2m/θ > 2` — this says the route sits exactly on the
boundary. Everything below `2` is reachable and useless; only strictly above `2` would help.

Three consequences worth stating plainly.

* **No constant below 2 can be proved.** Any attempt to close this route by a
  Cauchy–Schwarz-type bound `J₁ + J₂ ≤ c · I` with `c < 2` is refuted by this theorem. The
  crude Cauchy–Schwarz bound on `2·R₂` gives about `4`; the true answer is at least `2`; the
  only bound that both holds and closes the route is exactly `2`.
* **The `ε`-dependence is trivial.** The witnesses below satisfy the marginal conditions for
  every `ε` simultaneously, so no choice of `ε` in `(0,1)` is better than any other. That
  removes one of the two parameters from the search.
* **The remaining question is a single number.** Is the supremum exactly `2`, or greater?
  Only the second would give the twin prime conjecture under GEH.

## The witness, and why it is admissible

Fix `d ∈ (0, 1-ε]`. Take `F` to be a product: the indicator of `[0, 2-d)` in `t₁`, times
`+1` on `[0, d/2)` and `−1` on `[d/2, d)` in `t₂`. It is a thin horizontal strip spanning
almost the full width of the region, with its sign flipped halfway up.

* Support: `t₁ < 2-d` and `t₂ < d` give `t₁ + t₂ < 2`, so `F` lives in `2·R₂`.
* The `t₂`-marginal is `∫ F dt₂ = 0` for **every** `t₁`, because the sign flip cancels
  exactly. So the second vanishing-marginal condition holds trivially, for every `ε`, and
  `J₂(F) = 0` exactly.
* The `t₁`-marginal is `±(2-d)` on `[0, d)` and `0` elsewhere, so the first vanishing
  marginal condition holds whenever `d ≤ 1 + ε`, and `J₁(F) = (2-d)² d` whenever `d ≤ 1-ε`.
* `I(F) = (2-d) d`, so the ratio is exactly `2 - d`.

Letting `d ↓ 0` drives the ratio to `2` from below. Note the ratio is `< 2` for every `d > 0`:
the supremum `2` is approached and never attained by this family.

## What this does not say

It does not prove the supremum equals `2`, and therefore does not close
`TwinPrimesGEHMarginalRoute`. It does not touch the twin prime conjecture, GEH, or any bound
on `H₁`. Polymath8b's Theorem 3.14 is not formalised and is not used: the statement below is
a self-contained fact about integrals.
-/

namespace Statements.TwinPrimesGEHMarginalSharp

open MeasureTheory

/-- The canonical proposition: for every `ε ∈ (0,1)` and every `c < 2` there is a
square-integrable `F : ℝ → ℝ → ℝ` supported on `{t₁ + t₂ ≤ 2} ∩ [0,∞)²`, with all slices
integrable and both marginals vanishing beyond `1 + ε`, with `I(F) > 0` and

`c · I(F) < J_{1,1-ε}(F) + J_{2,1-ε}(F)`.

Equivalently: the supremum of the `k = 2` Polymath8b Theorem 3.14 ratio is at least `2`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ c : ℝ, c < 2 →
    ∃ F : ℝ → ℝ → ℝ,
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) ∧
      Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) ∧
      (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) ∧
      (∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂)) ∧
      (∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂)) ∧
      (∀ t₂ : ℝ, 1 + ε < t₂ → (∫ t₁, F t₁ t₂) = 0) ∧
      (∀ t₁ : ℝ, 1 + ε < t₁ → (∫ t₂, F t₁ t₂) = 0) ∧
      0 < (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume)) ∧
      c * (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume))
        < (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, F t₁ t₂) ^ 2)
          + (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, F t₁ t₂) ^ 2)

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesGEHMarginalSharp
