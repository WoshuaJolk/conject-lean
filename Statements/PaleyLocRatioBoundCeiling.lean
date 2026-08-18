import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocRatioBoundCeiling — the Hoffman ratio bound is pinned at `[1/2, 1]`

Both published ends of the window `c = lim ϑ(Ḡ_{p,1})/√p ∈ [1/2, 1]` come from the Hoffman
ratio bound applied to the Paley 1-localization `G_{p,1}` and to its complement, together
with Lovász's `ϑ(G)ϑ(Ḡ) = n` for vertex-transitive `G`.  Concretely, if
`μ = -λ_min(G_{p,1})` and `ν = max_{j ≠ 0} λ_j(G_{p,1})` then the ratio bound gives

    1 + d/μ  ≤  ϑ(Ḡ_{p,1})  ≤  m(1 + ν)/(m - d + ν),     m = (p-1)/2, d = (p-5)/4,

and those two expressions tend to `√p/2` and `√p` exactly when `μ, ν ~ √p/2`.

This statement asserts that `μ` and `ν` really are asymptotically `√p/2` — that the extreme
eigenvalues sit at the Weil boundary and do not retreat from it.  Consequently the ratio
bound **cannot** be pushed to the conjectured `1/√2` from either side: the window `[1/2, 1]`
is not a weakness of how the bound was applied, it is the bound's exact output on this graph.

## Why this is expected to be true, and what it would take to prove

The nontrivial eigenvalues of `G_{p,1}` are indexed by the multiplicative characters `ψ` of
the group of nonzero squares, and satisfy `λ_ψ = (-1 + √p · cos θ_ψ)/2` where `θ_ψ` is the
argument of a Jacobi sum of modulus `√p` — so `|λ_ψ| ≤ (√p + 1)/2` by Weil, with equality
approached exactly when some `θ_ψ` approaches `0` or `π`.  Katz's equidistribution theorem
for Jacobi-sum angles makes the `θ_ψ` equidistribute on the circle as `p → ∞`, and there are
`(p-1)/2` of them, so both extremes are approached.  A proof therefore needs an
equidistribution input, not merely the Weil bound.

Numerically the claim is emphatic: writing `ρ_ψ = (2λ_ψ + 1)/√p ∈ [-1, 1]`, at `p = 20021`
one finds `max ρ = 0.9999997` and `min ρ = -1.0000000`, with 492 characters above `0.99` and
472 below `-0.99`; the empirical distribution of `ρ` matches the arcsine law to three digits
(`E[ρ²] = 0.49994`, `E[ρ⁴] = 0.3734` against `1/2` and `3/8`) at `p = 8009`.

## Term-by-term read-back

* `A` is pinned to be the 0/1 adjacency matrix of `Commons.paleyLocAdj p` by the two
  hypotheses `adj u v → A u v = 1` and `¬ adj u v → A u v = 0`; nothing else is assumed of it.
* `z` ranges over real vectors on the vertex set with `∑ z = 0` (orthogonal to the all-ones
  vector, which carries the trivial eigenvalue `d`) and `∑ z² = 1` (unit length).
* `∑ᵤ∑ᵥ Aᵤᵥ zᵤ zᵥ` is the Rayleigh quotient of the adjacency operator at `z`.
* The two conjuncts say the Rayleigh quotient gets within a factor `1 - ε` of `-√p/2` and of
  `+√p/2` respectively — i.e. `λ_min ≤ -(1-ε)√p/2` and `λ_max' ≥ (1-ε)√p/2`.
* `N` is outside the `∀ p`, so it may not depend on `p`.

This is a **ceiling on a method**, not a bound on `c`.  It subtracts nothing from the answer
space: it says the ratio bound has already given everything it can, and that any advance on
`c` must come from a certificate that reads more of the spectrum than one extreme eigenvalue.
-/

namespace Statements.PaleyLocRatioBoundCeiling

/-- The canonical proposition: both extreme nontrivial eigenvalues of the Paley
1-localization are asymptotically `±√p/2`, so the Hoffman ratio bound is pinned at the
published window `[1/2, 1]` from both sides. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ _ : NeZero p, Nat.Prime p → p % 4 = 1 → N < p →
    ∀ A : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ,
      (∀ u v, Commons.paleyLocAdj p u v → A u v = 1) →
      (∀ u v, ¬ Commons.paleyLocAdj p u v → A u v = 0) →
      (∃ z : Commons.PaleyLocV p → ℝ, (∑ u, z u) = 0 ∧ (∑ u, z u ^ 2) = 1 ∧
        (∑ u, ∑ v, A u v * z u * z v) ≤ -(1 - ε) * Real.sqrt p / 2) ∧
      (∃ z : Commons.PaleyLocV p → ℝ, (∑ u, z u) = 0 ∧ (∑ u, z u ^ 2) = 1 ∧
        (1 - ε) * Real.sqrt p / 2 ≤ (∑ u, ∑ v, A u v * z u * z v))

/-- The open target. -/
theorem target : statement := sorry

end Statements.PaleyLocRatioBoundCeiling
