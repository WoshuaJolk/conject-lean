import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocSecondMomentBound — Problem 26's upper half, reduced to one spectral quantity

`Commons.paleyLocTheta p` is the quantity of this problem's root: `ϑ` of the complement of
the Paley 1-localization `G_{p,1}`.  Two classical counts describe that graph — it has
`m = (p-1)/2` vertices and is regular of degree `d = (p-5)/4` — and this statement takes
both as hypotheses, so that the arithmetic input is explicit and separable from the
semidefinite input.

The semidefinite input is a single real number `c`.  Let `R` be any symmetric matrix that
vanishes on the diagonal and, on every edge `uv`, records the deviation
`|N(u) ∩ N(v)| - d²/m` of the common-neighbour count from its average.  Off the edges `R` is
free — no condition is imposed there, and choosing a good completion is exactly what makes
`c` small.  Then

    paleyLocTheta p  ≤  2 + √(p/2 + 4c).

So `c = o(p)` gives `limsup ϑ(Ḡ_{p,1}) / √(p/2) ≤ 1`, which is the upper half of
Randomstrasse101 Problem 26 — the half that would give a purely semidefinite proof of a
Hanson–Petridis-strength clique bound for the Paley graph.  Conversely `c = p/8` returns the
already-published `√p`, so `c` is the entire remaining gap on that side, and any `c ≤ γp`
with `γ < 1/8` is a strict improvement on the published constant.

Why `c` is the right thing to attack: on a strongly regular graph the common-neighbour count
is constant on edges, `R` can be taken to be a multiple of the adjacency matrix, and the
resulting bound is asymptotically sharp — on the Paley graph itself it returns exactly `√p`.
`G_{p,1}` fails strong regularity by exactly one arithmetic quantity: for adjacent `u, v` the
count `|N(u) ∩ N(v)|` equals `p/8` plus one eighth of the character sum
`∑ₐ χ(a(a-1)(x-a))`, a Frobenius trace of the Legendre elliptic curve, bounded by `2√p` by
Hasse.  Bounding `c` is therefore a two-variable character-sum problem, not a further
semidefinite one.

## Term-by-term read-back

* `p` prime with `p % 4 = 1` and `5 < p`; `NeZero p` is an instance binder only so that
  `Commons.PaleyLocV p` elaborates, and is implied by primality.
* `(Fintype.card (Commons.PaleyLocV p) : ℝ) = ((p:ℝ) - 1)/2` — the vertex count `m`.
* `A` is pinned to the 0/1 adjacency matrix of `Commons.paleyLocAdj p` by the pair of
  hypotheses `adj u v → A u v = 1` and `¬ adj u v → A u v = 0`.
* `∀ u, ∑ v, A u v = ((p:ℝ) - 5)/4` — `d`-regularity with the classical degree.
* `R` — diagonal zero, and on every edge equal to `(A*A) u v - d²/m`.  `(A*A) u v` is the
  number of common neighbours of `u` and `v`.  Free off the edges.
* `(c • 1 - R).PosSemidef` — `c` dominates the top eigenvalue of `R`.
* the conclusion — `Commons.paleyLocTheta p hp.pos ≤ 2 + Real.sqrt ((p:ℝ)/2 + 4*c)`, with
  `paleyLocTheta` the problem's own quantity, unmodified.

## What this does not say

It supplies the implication only.  It asserts nothing about how small `c` can be made; that
is the open part.  It is an upper bound only — nothing is claimed below.  It does not assume
the limit `lim ϑ/√p` exists, and it says nothing about Schrijver's `ϑ'`, the 2-localization,
or prime-power order.  It is not vacuous: for every such `p` the hypotheses on `A` determine
a unique matrix, the two arithmetic hypotheses are classical facts about the Paley
1-localization, and `R` may be taken to be the deviation on edges and zero elsewhere with `c`
its largest eigenvalue.
-/

namespace Statements.PaleyLocSecondMomentBound

/-- The canonical proposition: the upper half of Problem 26 reduced to one spectral
quantity `c` attached to the common-neighbour counts of the Paley 1-localization. -/
abbrev statement : Prop :=
  ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p % 4 = 1 → 5 < p →
    ∀ (A R : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (c : ℝ),
      (Fintype.card (Commons.PaleyLocV p) : ℝ) = ((p : ℝ) - 1) / 2 →
      (∀ u v, Commons.paleyLocAdj p u v → A u v = 1) →
      (∀ u v, ¬ Commons.paleyLocAdj p u v → A u v = 0) →
      (∀ u, ∑ v, A u v = ((p : ℝ) - 5) / 4) →
      (∀ u, R u u = 0) →
      (∀ u v, Commons.paleyLocAdj p u v →
        R u v = (A * A) u v - (((p : ℝ) - 5) / 4) ^ 2 / (((p : ℝ) - 1) / 2)) →
      (c • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - R).PosSemidef →
      Commons.paleyLocTheta p hp.pos ≤ 2 + Real.sqrt ((p : ℝ) / 2 + 4 * c)

/-- The open target. -/
theorem target : statement := sorry

end Statements.PaleyLocSecondMomentBound
