import Mathlib

/-!
# ExpLattice4Base2At24 — `h(L₄(2)) ≥ 24`

The `24` permutations of `(2⁰, 2¹, 2², 2³)` form an empty polytope of the exponential
lattice `L₄(2) = {2ⁿ : n ∈ ℕ₀}⁴`, so `h(L₄(2)) ≥ 4! = 24`.

This is the first dimension in which the factorial construction beats the published bound.
The best lower bound in the literature is `5 · 2^(d-2) = 20` at `d = 4`, from the product
bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di Summa, Theorem 2.6 of De Loera–La
Haye–Oliveros–Roldán-Pensado, Adv. Geom. **17** (2017) 473–482) with `h(L₂(2)) = 5`
(Ambrus–Balko–Frankl–Jung–Naszódi, European J. Combin. **116** (2024) 103884, Corollary 4).
Arun–Dillon Theorem 1.2 gives `4` at `α = 2`.

This is the `d = 4` case of the statement `ExpLatticeFactorialLower`, `h(L_d(2)) ≥ d!`,
which is filed on the same problem and is not machine-checked in general: the general proof
needs the minimality of the binary representation among multisets of powers of two, whereas
at fixed `d` the bounding box is finite and the check is a finite certificate.
-/

namespace Statements.ExpLattice4Base2At24

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- There is an empty polytope with `24` vertices in `L₄(2)`; equivalently `h(L₄(2)) ≥ 24`. -/
abbrev statement : Prop :=
  ∃ V : Set (Fin 4 → ℝ), IsEmptyPolytope (expLattice 4 2) V ∧ V.ncard = 24

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ExpLattice4Base2At24
