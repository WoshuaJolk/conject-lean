import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Nat.Prime.Basic

/-!
# MaynardTaoM2CeilingAtTwo — the `k = 2` Maynard–Tao sieve criterion can never fire

This is a **method ceiling**, stated as two unconditional theorems.  Neither of them is about
the twin primes directly; together they say that one specific, named, published route to the
twin prime conjecture is closed, and they say it with a proof rather than a heuristic.

## The route being closed

Polymath8b (arXiv:1407.4897), Theorem 3.8, reads: let `k ≥ 2` and `m ≥ 1` be fixed integers;
for compactly supported square-integrable `F : [0,∞)^k → ℝ` put

* `I(F) := ∫_{[0,∞)^k} F²`,
* `J_i(F) := ∫_{[0,∞)^{k-1}} (∫_0^∞ F dt_i)²`,
* `M_k := sup (Σ_i J_i(F)) / I(F)` over `F` supported on the simplex
  `R_k := {t ∈ [0,∞)^k : t₁ + ⋯ + t_k ≤ 1}` and not a.e. zero.

If there is a fixed `0 < θ < 1` with `EH[θ]` and `M_k > 2m/θ`, then `DHL[k, m+1]` holds:
every admissible `k`-tuple has infinitely many translates containing at least `m+1` primes.
Applied to the admissible pair `{0, 2}`, `DHL[2,2]` **is** the twin prime conjecture.

The first conjunct below is `M₂ ≤ 2`.  Since `0 < θ < 1` forces `2m/θ > 2m ≥ 2`, the
hypothesis `M₂ > 2m/θ` of Theorem 3.8 is unsatisfiable.  The `k = 2` case of that criterion
cannot fire, for any `θ`, any `m`, and any `F` whatsoever — not because nobody has found a
good `F`, but because none exists.

The second conjunct is the bookkeeping that turns "`k = 2` is dead" into "no bound `H₁ ≤ 5`
is reachable this way": there is no admissible triple of diameter at most `5`, so any
`DHL[k,2]` yielding `H₁ ≤ 5` would have to use `k = 2`.

## Read back against the Lean, term by term

**Conjunct 1.**  `F : ℝ → ℝ → ℝ` is the curried `k = 2` test function; `Function.uncurry F`
is the function on `ℝ × ℝ` carrying Lebesgue measure `volume.prod volume`.  The three
hypotheses are exactly Polymath8b's admissible class: `F` is measurable, square-integrable,
and supported on `R₂` (`F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 1`; support is stated as a
vanishing condition off `R₂`, which is the same thing and needs no `Set` vocabulary).  The
conclusion `J₁(F) + J₂(F) ≤ 2 · I(F)` is the definition of `M₂ ≤ 2` unfolded: it is the
inequality for every admissible `F`, which is what a bound on the supremum means.  No `sup`
appears, deliberately — a `sSup` over an unbounded set of reals is `0` by Mathlib convention,
so quantifying over `F` avoids importing that convention into the claim.  `I` is written as a
genuine integral over `ℝ × ℝ`, not as an iterated integral, so it is Lebesgue measure on the
plane and not a Fubini artifact.

**Conjunct 2.**  Admissibility of `{h₁, h₂, h₃}` is `∀ p prime, ∃ a, p ∤ a + h₁ ∧ p ∤ a + h₂ ∧
p ∤ a + h₃`: the tuple misses at least one residue class mod every prime.  `h₁ < h₂ < h₃` and
`h₃ ≤ h₁ + 5` is "three distinct shifts of diameter at most 5".  The claim is that no such
triple is admissible.  The bound `5` is **sharp**: `{0, 2, 6}` is admissible and has diameter
`6`, so replacing `h₁ + 5` by `h₁ + 6` turns conjunct 2 into a false statement.

## What this does and does not close

It does **not** prove the twin prime conjecture false, does not move `H₁`'s upper bound of
`246`, and does not rule out sieve proofs in general.  Three things it explicitly leaves
standing, and which are the residual:

1. **Polymath8b Theorem 3.14 at `k = 2`.**  That criterion takes `F` supported on the larger
   region `(k/(k-1))·R_k = 2·R₂` subject to a vanishing-marginal condition, and uses the
   truncated functionals `J_{i,1-ε}`.  It is not the `M_k` criterion, is not bounded by `M₂`
   or `M_{2,ε}`, is formally available at `k = 2`, and is the criterion behind Polymath8b's
   own `H₁ ≤ 6` under GEH.  Nothing here touches it.
2. **Routes that do not go through `DHL[k,2]` at all**, such as Polymath8b Remark 8.1 and
   Proposition 9.1.
3. **Parity-breaking inputs**, which are known to exist in other settings: Heath-Brown's
   theorem that a Siegel zero implies infinitely many twin primes, and Sawin–Shusterman's
   unconditional twin prime theorem over `F_q[T]` for `q > 685090 p²`.

The heuristic parity barrier of Polymath8b Section 8 is what is usually cited for "sieves
cannot do this".  That section calls itself "somewhat informal and heuristic in nature".
This statement is the part of that folklore which is a theorem.
-/

namespace Statements.MaynardTaoM2CeilingAtTwo

open MeasureTheory

/-- The canonical proposition.

**(1)** `M₂ ≤ 2` for the Maynard–Tao/Polymath8b second-moment ratio: for every measurable,
square-integrable `F` supported on the simplex `R₂ = {(t₁,t₂) : 0 ≤ t₁, 0 ≤ t₂, t₁+t₂ ≤ 1}`,
`J₁(F) + J₂(F) ≤ 2 I(F)`.  Hence the hypothesis `M₂ > 2m/θ` of Polymath8b Theorem 3.8, which
requires `M₂ > 2` since `0 < θ < 1` and `m ≥ 1`, is unsatisfiable.

**(2)** No admissible triple has diameter at most `5`; the bound is sharp, since `{0,2,6}` is
admissible. -/
abbrev statement : Prop :=
  (∀ F : ℝ → ℝ → ℝ,
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) →
      (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 1) →
      (∫ t₂, (∫ t₁, F t₁ t₂) ^ 2) + (∫ t₁, (∫ t₂, F t₁ t₂) ^ 2)
        ≤ 2 * ∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume)) ∧
  (∀ h₁ h₂ h₃ : ℕ, h₁ < h₂ → h₂ < h₃ → h₃ ≤ h₁ + 5 →
      ¬ (∀ p : ℕ, Nat.Prime p →
          ∃ a : ℕ, ¬ p ∣ (a + h₁) ∧ ¬ p ∣ (a + h₂) ∧ ¬ p ∣ (a + h₃)))

/-- The open target. -/
theorem target : statement := sorry

end Statements.MaynardTaoM2CeilingAtTwo
