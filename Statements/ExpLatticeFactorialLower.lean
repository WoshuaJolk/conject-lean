import Mathlib

/-!
# ExpLatticeFactorialLower — `h(L_d(2)) ≥ d!`

The best lower bound in the literature for the Helly number of the `d`-dimensional
exponential lattice `L_d(2) = {2ⁿ : n ∈ ℕ₀}^d` is `5 · 2^(d-2)`, from the product bound
`h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di Summa, Theorem 2.6 of De Loera–La
Haye–Oliveros–Roldán-Pensado, Adv. Geom. **17** (2017) 473–482) together with
`h(L₂(2)) = 5` (Ambrus–Balko–Frankl–Jung–Naszódi, European J. Combin. **116** (2024)
103884, Corollary 4).  Arun–Dillon's Theorem 1.2 gives only `d` at `α = 2`.  Both are at
most exponential in `d`.

This statement asserts `h(L_d(2)) ≥ d!`, which is super-exponential and overtakes
`5 · 2^(d-2)` from `d = 4` on (`24 > 20`, `120 > 40`, `720 > 80`, …).

**The construction.**  Take the `d!` points obtained by permuting the coordinates of
`(2⁰, 2¹, …, 2^(d-1))`.

*Contained in the lattice*: each coordinate is a power of two.

*Empty*: every one of these points has coordinate sum `2⁰ + 2¹ + ⋯ + 2^(d-1) = 2^d - 1`,
so their convex hull lies inside the hyperplane `Σ xᵢ = 2^d - 1`, and a lattice point in
the hull is a `d`-tuple of powers of two summing to `2^d - 1`.  A multiset of powers of two
summing to `N` has at least `popcount N` elements, with equality only for the binary
representation; here `popcount (2^d - 1) = d` and the multiset has exactly `d` elements, so
it is `{2⁰, …, 2^(d-1)}` and the point is one of the `d!` permutations.  Nothing else is in
the hull.

*Convex position*: these are the vertices of a permutohedron.  Concretely, for the point
`v` given by the permutation `σ`, the integer functional `x ↦ Σᵢ σ(i)·xᵢ` is maximised over
the `d!` points uniquely at `v`, by the rearrangement inequality, since the coefficient
vector and the coordinate vector are then equally ordered and the values `2⁰, …, 2^(d-1)`
are pairwise distinct.

Verified in exact integer arithmetic for `d ≤ 5`: `|V| = d!`, the number of lattice points
of `L_d(2)` on the hyperplane is exactly `d!` with no extras, and convex position holds by
an exact rational LP on every point against the hull of the others.

**Filed unproved in Lean.**  The mathematics above is complete and elementary, but nothing
in this module has been machine-checked; the `popcount` minimality lemma and the strict
rearrangement inequality are the two pieces a proof has to supply.  Self-assessed novelty
is moderate and is stated in the accompanying message: the construction is elementary and
the literature on this object is two papers deep, so "elementary and unwritten" is the
likely status rather than "hard and new".
-/

namespace Statements.ExpLatticeFactorialLower

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- `h(L_d(2)) ≥ d!` in every dimension: the exponential lattice `{2ⁿ : n ∈ ℕ₀}^d` contains
an empty polytope with `d!` vertices. -/
abbrev statement : Prop :=
  ∀ d : ℕ, ∃ V : Set (Fin d → ℝ),
    IsEmptyPolytope (expLattice d 2) V ∧ V.ncard = Nat.factorial d

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLatticeFactorialLower
