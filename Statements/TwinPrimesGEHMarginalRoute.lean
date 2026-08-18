import Mathlib.MeasureTheory.Integral.Prod

/-!
# TwinPrimesGEHMarginalRoute — the one `k = 2` sieve criterion nobody has closed

This is an **open target**, filed as the residual of the `M₂ ≤ 2` ceiling.  It is the exact
`k = 2` specialisation of Polymath8b (arXiv:1407.4897) Theorem 3.14, the criterion the
authors introduced to go *beyond* the `M_k` and `M_{k,ε}` variational problems.  Unlike
`M₂` and `M_{2,ε}`, which the paper evaluates in closed form (`M₂ = 1/(1-W(1/e)) = 1.38593…`,
Corollary 6.3; `M_{2,ε} = (e(1+ε)-2ε)/(e-1) < 2` for `ε < 1`, pp. 46-47), the functional
below is **never named, never symbolised and never bounded anywhere in that paper, at any
`k`**.  Section 8's parity discussion predicts it cannot exceed `2`, and that discussion
calls itself "somewhat informal and heuristic in nature".

## Why this proposition matters

Polymath8b Theorem 3.14 at `k = 2`, `m = 1`: let `0 < θ < 1` with `GEH[θ]`, let `0 < ε < 1`
(the constraint is `ε < 1/(k-1)`, which at `k = 2` is exactly `ε < 1`), and suppose there is
a non-zero square-integrable `F : [0,∞)² → ℝ` supported in `2 · R₂ = {t₁ + t₂ ≤ 2}` with the
vanishing marginal condition `∫₀^∞ F dt_i = 0` whenever the other variable exceeds `1 + ε`,
such that `(J_{1,1-ε}(F) + J_{2,1-ε}(F)) / I(F) > 2m/θ`.  Then `DHL[2,2]` holds — and
`DHL[2,2]` applied to the admissible pair `{0,2}` **is** the twin prime conjecture.

Since `2m/θ = 2/θ` decreases to `2` as `θ ↑ 1`, a single pair `(ε, F)` with ratio strictly
greater than `2` would give: **GEH implies the twin prime conjecture.**  That is what the
proposition below asserts the existence of.

Three radii are in play and they are all different; getting them confused is the way to file
the wrong statement, so they are named here.  Support radius `k/(k-1) = 2`.  Marginal
vanishing threshold `1 + ε`.  Truncation radius of the `J` integrals `1 - ε`, whose region
`(1-ε)·R_{k-1}` at `k = 2` is the interval `[0, 1-ε]`.  `I(F)` is **not** truncated: it is
`∫_{[0,∞)²} F²` over the whole support.  That asymmetry between `I` and `J` is the entire
content of the criterion.

## Read back against the Lean, term by term

`F : ℝ → ℝ → ℝ` curried; `Function.uncurry F` carries Lebesgue measure on `ℝ × ℝ`.
`hsupp` is support in `2 · R₂`, written as a vanishing condition off the region.
`hslice₁`, `hslice₂` require every slice to be integrable.  This is a **strengthening** of
Theorem 3.14's hypotheses, deliberately: Lean's Bochner integral returns `0` on a
non-integrable function, so without it the vanishing-marginal conditions could be satisfied
by a junk value rather than by an actual cancellation, and the target would be satisfiable
for a reason with no sieve-theoretic meaning.  Requiring integrability makes the existence
claim strictly harder, which is the safe direction, and costs nothing: the only known
candidate constructions (Polymath8b Theorem 3.15 at `k = 3`) are compactly supported
piecewise polynomials, all of whose slices are integrable.

`hmarg₁`, `hmarg₂` are eq. (35).  The final inequality is
`2 · I(F) < J_{1,1-ε}(F) + J_{2,1-ε}(F)`, i.e. ratio `> 2`.  Nothing forces `I(F) > 0`
separately: if `F` were a.e. zero both sides would be `0` and the strict inequality would
fail, so non-triviality is already implied.

## What resolving this does, in either direction

* **Proved** (some `(ε, F)` exists): with Polymath8b Theorem 3.14 and GEH — neither of which
  is formalised — the twin prime conjecture follows.  This is a construction problem, and it
  has a precedent: Theorem 3.15 solves the `k = 3` analogue with an explicit piecewise
  polynomial on 60 polyhedra, achieving ratio `2 + 286648173/4966595189139280`, a margin of
  `5.8 × 10⁻⁸`.  Any search here must be exact-rational, not floating point.
* **Refuted** (no such `(ε, F)`): the rigorous `k = 2` counterpart of Corollary 6.3, and the
  last `M`-type route to `H₁ = 2` closes with a proof rather than a heuristic.

Both are results.  The parity heuristic predicts the second.  Nobody has proved either.
-/

namespace Statements.TwinPrimesGEHMarginalRoute

open MeasureTheory

/-- The canonical proposition: there exist `0 < ε < 1` and a square-integrable
`F : ℝ → ℝ → ℝ` supported on `{t₁ + t₂ ≤ 2} ∩ [0,∞)²`, with all slices integrable and with
both marginals vanishing beyond `1 + ε`, whose truncated second-moment ratio exceeds `2`:

`2 · ∫ F² < ∫_{t₂ ≤ 1-ε} (∫ F dt₁)² dt₂ + ∫_{t₁ ≤ 1-ε} (∫ F dt₂)² dt₁`.

This is Polymath8b Theorem 3.14 at `k = 2`, `m = 1`, in the limit `θ ↑ 1`. -/
abbrev statement : Prop :=
  ∃ (ε : ℝ) (F : ℝ → ℝ → ℝ),
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

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesGEHMarginalRoute
