import Mathlib

/-!
# ExpLatticeScalingBarrier — a scaling orbit contributes at most two vertices

Let `L₃(α) = {αⁿ : n ∈ ℕ₀}³ ⊆ ℝ³` and let `V` be an empty polytope of `L₃(α)` in the sense
of Ambrus–Balko–Frankl–Jung–Naszódi.  The exponential lattice has essentially one symmetry
available for building large configurations: for any subset `S` of the coordinates, the
diagonal map that multiplies the coordinates in `S` by `α` and fixes the rest sends
`L₃(α)` into itself and is linear, hence preserves convex hulls.  Iterating such a map is
the natural way to try to produce empty polytopes of unbounded size — a self-similar,
scale-invariant family.

This statement closes that route.  Fix a point `u` and a nonempty set `S` of coordinates,
encoded as `s : Fin 3 → Bool`, and consider the orbit `n ↦ (α ^ n on S, identity off S)·u`.
At most two of its members can lie in `V`, and no two members whose exponents differ by
`2` or more can both lie in `V`.

The mechanism is one line.  If `u ∈ V` and the `α ^ d`-scaled copy is also in `V` with
`d ≥ 2`, then the `α`-scaled copy `w` is again a point of `L₃(α)`, and
`w = (1 - t)·u + t·(α ^ d-scaled copy)` for `t = (α - 1)/(α ^ d - 1) ∈ (0,1)`.  So `w` lies
in `conv V ∩ L₃(α) ⊆ V`, and then `w` is a point of `V` in the convex hull of the others,
contradicting convex position.

Two special cases are worth naming.  `S` = all three coordinates gives: at most two
vertices on any ray through the origin, at consecutive scales.  `S` a single coordinate
gives: at most two vertices on any axis-parallel line, at consecutive scales.  Together
they say that any family of empty polytopes with unboundedly many vertices must use
unboundedly many distinct directions; no bounded set of directions, scaled, will do.
-/

namespace Statements.ExpLatticeScalingBarrier

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- A scaling orbit meets an empty polytope in at most two points, and never in two points
whose exponents differ by two or more. -/
abbrev statement : Prop :=
  ∀ α : ℝ, 1 < α → ∀ V : Set (Fin 3 → ℝ), IsEmptyPolytope (expLattice 3 α) V →
    ∀ (u : Fin 3 → ℝ) (s : Fin 3 → Bool) (i₀ : Fin 3), s i₀ = true →
      {n : ℕ | (fun i => (if s i then α ^ n else 1) * u i) ∈ V}.ncard ≤ 2 ∧
      ∀ d : ℕ, 2 ≤ d → u ∈ V →
        (fun i => (if s i then α ^ d else 1) * u i) ∈ V → False

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLatticeScalingBarrier
