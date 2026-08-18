import Mathlib.MeasureTheory.Integral.Prod

/-!
# TwinPrimesGEHMarginalCeiling — the target that would close the last M-type route

This is the upper bound matching the proved lower bound of `TwinPrimesGEHMarginalSharp`, and
the negation of `TwinPrimesGEHMarginalRoute`.  Together the three say:

* `TwinPrimesGEHMarginalSharp` (**proved**): the supremum of the `k = 2` Polymath8b
  (arXiv:1407.4897) Theorem 3.14 ratio is at least `2`, for every `ε ∈ (0,1)`.
* `TwinPrimesGEHMarginalRoute` (**open**): is it strictly greater than `2` for some `ε`?  If
  yes, then GEH implies the twin prime conjecture, by Theorem 3.14 at `k = 2`, `m = 1`.
* **this statement** (**open**): is it at most `2` for every `ε`?  If yes, the `k = 2`
  criterion can never fire, and the last variational route in Polymath8b to `H₁ = 2` closes
  with a proof rather than with the heuristic parity argument of that paper's Section 8.

Proving this proposition is therefore the rigorous `k = 2` counterpart of Polymath8b
Corollary 6.3 (`M₂ = 1/(1-W(1/e))`) and Corollary 6.4 (`M₂ ≤ 2 log 2`), neither of which
covers the Theorem-3.14 functional: those bound `M_k` and `M_{k,ε}`, whose test functions
live on `R_k` and `(1+ε)·R_k`, while this functional's live on the strictly larger `2·R₂`
with a vanishing-marginal constraint.  Nothing in that paper bounds it, at any `k`.

## Why the obvious proof does not work

Slicewise Cauchy–Schwarz bounds `J_{1,1-ε}(F)` by `∫ (2-t₂) 1_{t₂ ≤ 1-ε} F²` and
`J_{2,1-ε}(F)` by `∫ (2-t₁) 1_{t₁ ≤ 1-ε} F²`.  The total pointwise weight is `4 - t₁ - t₂`
on the square `[0,1-ε]²`, which is at least `2 + 2ε`.  So the pointwise argument gives about
`4`, not `2`, and it must fail: dropping the marginal constraint entirely makes the
supremum genuinely exceed `2` — the constant function on `2·R₂` already gives ratio
`7/3 / 1 > 2` at `ε → 0`, and it is exactly the marginal constraint that excludes it.  Any
proof must therefore use the constraint globally rather than slice by slice.

## Numerical evidence

Discretising the constrained problem and computing the exact top eigenvalue of the quadratic
form on the null space of the marginal constraints — the constrained rows and constrained
columns are variable-disjoint, so that projection is orthogonal and the discrete maximum is
exact — returns `2.0000000000` for `ε ∈ {0.05, 0.1, 0.25, 0.5, 0.75, 0.9}` at `120`, `200`
and `300` cells per side, the only departures being `+h` exactly, a grid-alignment artifact.
That is evidence, not a proof, and it is recorded here as evidence.

## What proving this does not do

It does not refute the twin prime conjecture, does not move `H₁`, and does not close sieve
methods in general.  Routes that do not pass through `DHL[k,2]` (Polymath8b Remark 8.1,
Proposition 9.1) and parity-breaking inputs (Heath-Brown's Siegel-zero theorem;
Sawin–Shusterman over `F_q[T]`) are untouched by it.
-/

namespace Statements.TwinPrimesGEHMarginalCeiling

open MeasureTheory

/-- The canonical proposition: for every `ε ∈ (0,1)` and every square-integrable `F` supported
on `{t₁ + t₂ ≤ 2} ∩ [0,∞)²` whose slices are integrable and whose marginals vanish beyond
`1 + ε`,

`J_{1,1-ε}(F) + J_{2,1-ε}(F) ≤ 2 · I(F)`.

By `TwinPrimesGEHMarginalSharp` the constant `2` cannot be replaced by anything smaller. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ F : ℝ → ℝ → ℝ,
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) →
      (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) →
      (∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂)) →
      (∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂)) →
      (∀ t₂ : ℝ, 1 + ε < t₂ → (∫ t₁, F t₁ t₂) = 0) →
      (∀ t₁ : ℝ, 1 + ε < t₁ → (∫ t₂, F t₁ t₂) = 0) →
      (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, F t₁ t₂) ^ 2)
        + (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, F t₁ t₂) ^ 2)
        ≤ 2 * ∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume)

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesGEHMarginalCeiling
