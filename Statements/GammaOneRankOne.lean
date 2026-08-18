import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# GammaOneRankOne — the period lattice contains no nonzero element of rank at most two

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this says

`Γ₁ ⊆ Γ₂ ⊗ Γ_p` is spanned by the four columns of Zharkov's polarisation matrix `Q`.  A
*rank-one* element of `Γ₂ ⊗ Γ_p` is one of the form `u ⊗ s`; these are exactly the possible
edge displacements of a tropical chain, since an edge has one integral slope `u ∈ Γ₂` and one
length `s ∈ Γ_p`.  The statement is:

  for every `d > 0`, two rank-one elements congruent modulo `Γ₁` are **equal**.

Equivalently: `Γ₁` meets the set of elements of rank `≤ 2` only in `0`.  (A difference of two
rank-one matrices is exactly an element of rank `≤ 2`.)

## Why it matters on this problem

`KontsevichPhiIffLattice` reduces the root question to a statement about the group of
tautological classes of **balanced chains**, and by `KontsevichChainVolVanishes` every class in
that group comes from a chain that *wraps*: one whose flags only cancel after the vertices are
read modulo `Γ₁`.  This statement says how expensive wrapping is.

* No single parallelogram wraps.  A parallelogram closes up in `X = V/Γ₁` only if both of its
  side vectors `u ⊗ s` and `v ⊗ t` lie in `Γ₁`, and rank-one elements of `Γ₁` are `0`.
* No `2`-dimensional tropical subtorus exists.  A subtorus with `Γ₂`-rational slopes needs a
  rank-`2` sublattice of `Γ₁` inside `Λ ⊗ Γ_p` for a rank-`2` `Λ ⊆ Γ₂`, and every element of
  such a sublattice has rank `≤ 2`.
* In any tropical curve or chain, the edge from one vertex class to another is **unique**: two
  edges joining the same pair of classes have the same displacement in `Γ₂ ⊗ Γ_p`, not merely
  the same displacement modulo `Γ₁`.  So the quotient graph of a tropical curve is simple, and
  every vertex of valence two is straight.
* Any closed loop with nontrivial holonomy therefore needs at least **three** edges with
  linearly independent slopes, since a nonzero element of `Γ₁` is a sum of at least three
  rank-one elements.

Those four consequences are the reason a wrapping chain cannot be small, and they are the
residual this statement hands to a search: any construction of a nonzero balanced chain must
use at least three independent slope directions and cannot be planar.

## The proof, in one paragraph

If `u ⊗ s - v ⊗ t = Σ nᵢ γᵢ`, every `3 × 3` minor of the left side vanishes, because a
difference of two rank-one matrices has rank `≤ 2`.  Four particular minors of the right side
are, in the coordinates `n = (n₀, n₁, n₂, n₃)`,

  `n₀ (n₀² + d n₂²)`,  `-d n₂ (n₀² + d n₂²)`,  `-n₁ (n₁² + d n₃²)`,  `d n₃ (n₁² + d n₃²)`.

With `d > 0` the first two force `n₀² + d n₂² = 0`, hence `n₀ = n₂ = 0`, and the last two force
`n₁ = n₃ = 0`.  So the element is `0`.  Nothing analytic and nothing about `θ`, `w₁`, `w₂`
enters; the whole content is the shape of `Q`.

## What is not claimed

Nothing about rank `3`: `γ₁ = e₁ ⊗ a + e₂ ⊗ b + e₄ ⊗ e` has rank exactly `3`, so the bound is
sharp and three-term decompositions do exist.  Nothing about whether wrapping chains exist.
-/

namespace Statements.GammaOneRankOne

open MvPolynomial

/-- The lattice `Γ₂` of integral slopes. -/
abbrev G2 : Type := Fin 4 → ℤ

/-- The parameter lattice `Γ_p = ℤ⟨a, b, c, e⟩`. -/
abbrev Gp : Type := Fin 4 → ℤ

/-- `Γ₂ ⊗ Γ_p`, rows indexed by the basis of `Γ₂`, columns by the basis of `Γ_p`. -/
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

/-- `u ⊗ s ∈ Γ₂ ⊗ Γ_p`; Zharkov writes this `su`.  The rank-one elements are exactly these. -/
def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

/-- The four columns of Zharkov's polarisation matrix `Q`, read as elements of `Γ₂ ⊗ Γ_p`.
They span `Γ₁`. -/
def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

/-- The period lattice `Γ₁ ⊆ Γ₂ ⊗ Γ_p`. -/
noncomputable def gammaOne (d : ℤ) : Submodule ℤ G2P :=
  Submodule.span ℤ (Set.range (gammaGen d))

/-- The canonical proposition.  This is the type the verifier demands.

For every positive `d`, two rank-one elements of `Γ₂ ⊗ Γ_p` that are congruent modulo the
period lattice `Γ₁` are equal.  Equivalently, `Γ₁` contains no nonzero element of rank at
most two. -/
abbrev statement : Prop :=
  ∀ (d : ℤ), 0 < d → ∀ (u v : G2) (s t : Gp),
    outer u s - outer v t ∈ gammaOne d → outer u s = outer v t

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.GammaOneRankOne
