import Mathlib

/-!
# ExpLatticeSliceReduction — coordinate slices of an empty polytope of `L₃(α)`

The open problem of Ambrus–Balko–Frankl–Jung–Naszódi (European J. Combin. **116** (2024)
103884, arXiv:2301.04683v4, "Open problems"), restated as Problem 1 of Arun–Dillon
(arXiv:2409.07262v2), asks whether the Helly number `h(L₃(a))` of the three-dimensional
exponential lattice `L₃(a) = {a ⁿ : n ∈ ℕ₀}³` is finite.  Everything published on it is a
*lower* bound: no finite upper bound is known in any dimension above two, for any base.

This statement is an upper-bound tool.  It says two things, and the second follows from
the first by counting.

1. **Fibre.**  For every `c`, the set of vertices of an empty polytope of `L₃(α)` whose
   last coordinate equals `c`, projected to the first two coordinates, is an empty
   polytope of the *planar* exponential lattice `L₂(α)`.  Nothing about `α` is used: the
   argument is that a coordinate hyperplane is convex, so the fibre inherits both convex
   position and emptiness, and the projection is injective on a fibre because the
   discarded coordinate is constant there.

2. **Count.**  Hence if every empty polytope of `L₂(α)` has at most `N` vertices, then
   every empty polytope of `L₃(α)` has at most `N` times as many vertices as it has
   distinct last coordinates.

Ambrus–Balko–Frankl–Jung–Naszódi prove `h(L₂(a)) < ∞` for every `a > 1`, with
`h(L₂(a)) = 5` for `a ≥ 2` (their Theorem 2 and Corollary 4).  Feeding `N = 5` into (2)
gives, for `a = 2`: every empty polytope of `L₃(2)` has at most `5 m` vertices, where `m`
is the number of distinct values taken by any one coordinate.  In particular the box
maximum `f(M)` — the largest empty polytope with all exponents at most `M` — satisfies
`f(M) ≤ 5 (M + 1)`, which is the first upper bound of any kind recorded for this problem,
and `h(L₃(a))` is finite **if and only if** the number of distinct values of a single
coordinate on an empty polytope of `L₃(a)` is bounded.

The same proof applies verbatim to the planes `{x = α ᵈ y}`, `{x = α ᵈ z}`, `{y = α ᵈ z}`,
because each meets `L₃(α)` in an affine copy of `L₂(α)`; the statement below fixes the
coordinate hyperplane `{z = c}` for definiteness.

The definitions are the same as in the root statement `ExpLatticeHellyFinite`, restated
here so that this module is self-contained.
-/

namespace Statements.ExpLatticeSliceReduction

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- Forget the last coordinate. -/
def pr (x : Fin 3 → ℝ) : Fin 2 → ℝ := ![x 0, x 1]

/-- Every `z`-fibre of an empty polytope of `L₃(α)` projects to an empty polytope of
`L₂(α)`; hence a bound `N` on planar empty polytopes bounds a spatial one by `N` times
its number of distinct last coordinates. -/
abbrev statement : Prop :=
  ∀ (α : ℝ) (V : Set (Fin 3 → ℝ)), IsEmptyPolytope (expLattice 3 α) V →
    (∀ c : ℝ, IsEmptyPolytope (expLattice 2 α) (pr '' {v | v ∈ V ∧ v 2 = c})) ∧
    ∀ N : ℕ, (∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N) →
      V.ncard ≤ N * ((fun v : Fin 3 → ℝ => v 2) '' V).ncard

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLatticeSliceReduction
