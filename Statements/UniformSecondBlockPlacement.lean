import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# UniformSecondBlockPlacement — one-sided coordinate genericity suffices for a phase placement

Convention (as in `CopiesTransversalCore`, `PhasePlacementUniform`, `MinorSplitPhaseTransversal`,
and opposite to Lovász–Saks–Schrijver): an edge of the orthogonality graph means the two vectors
*are* orthogonal.

Context. `MinorSplitPhaseTransversal` (jig.so/p/14?s=23) produces a phase placement from a finite
minor condition: for every pair of subfamilies, one split into rows from each side together with
*disjoint* column sets whose two square minors are both nonzero. That condition still quantifies
over pairs of subfamilies, and finding the split is the work. This statement discharges it from a
hypothesis on *one* of the two families alone.

The hypothesis. Call a family *coordinate-uniform* when every linearly independent set of its
vectors has *all* of its square minors nonzero — for `t` independent vectors, every choice of `t`
coordinates gives a nonzero determinant. Nothing is asked of dependent sets, and that restriction
is essential rather than cosmetic: in a `k`-regular orthogonality graph the `k` neighbours of a
vertex lie in that vertex's orthogonal complement, so those `k` vectors are dependent and their
full-size minors vanish under every invertible change of basis. Asking for all minors of all row
sets is therefore impossible for a seed, while asking it only of independent sets is a generic
condition, being the nonvanishing of finitely many polynomials that are not identically zero.

Why one side is enough. Given subfamilies `S` of the first family and `T` of the second, take *all*
`rk u S` independent vectors of the first, and choose coordinates for them by the elementary fact
that a family of rank `a` has some `a` coordinates on which it stays rank `a`. The second block then
needs `min k (rk u S + rk w T) - rk u S` further coordinates disjoint from those, and coordinate
uniformity makes *every* such choice work — so the split needs no search on the second side, and the
count of remaining coordinates always suffices. Neither family is asked for anything beyond having
no zero vector; for the second family that is not implied by uniformity, since a zero vector is
dependent on its own and so exempt, and it is what makes the size-one instances of uniformity bite
and give every entry of the second family nonzero — which is the shared-support condition for the
cross pairings.

Scope. Only diagonal phase placements. Nothing is claimed here about which families are
coordinate-uniform, nor about the fixed change of basis that arranges it for a given seed; that is
the remaining input, and it is a finite exact check per seed rather than a quantifier over phases.
Nothing is claimed for `k = 1`. The conclusion is the cross hypothesis of `CopiesTransversalCore`,
not a gadget and not a UPB.
-/

namespace Statements.UniformSecondBlockPlacement

variable {k : ℕ}

/-- The Hermitian pairing on `Fin k → ℂ`, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The rank of the subfamily of `v` indexed by a finite set `S`: the dimension of its span. -/
noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

/-- A phase vector: every coordinate has modulus one. -/
abbrev IsPhase (z : Fin k → ℂ) : Prop := ∀ r, ‖z r‖ = 1

/-- The phase placement of a family: scale coordinate `r` of every vector by `z r`. -/
abbrev scale {ι : Type} (z : Fin k → ℂ) (w : ι → Fin k → ℂ) : ι → Fin k → ℂ :=
  fun j r => z r * w j r

/-- Transversality of two blocks, the hypothesis consumed by `CopiesTransversalCore`. -/
abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) : Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

/-- Coordinate uniformity: every linearly independent selection of `t` vectors of the family has a
nonzero minor on *every* choice of `t` distinct coordinates. Dependent selections are exempt. -/
abbrev CoordinateUniform {n : ℕ} (w : Fin n → Fin k → ℂ) : Prop :=
  ∀ (t : ℕ) (b : Fin t → Fin n) (e : Fin t → Fin k),
    Function.Injective b → Function.Injective e →
    LinearIndependent ℂ (fun p => w (b p)) →
    Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0

/-- The canonical proposition.

Fix `k ≥ 2` and two families with no zero vector, the second coordinate-uniform. Then a single
phase vector makes every cross pairing between the two families nonzero and puts them in transversal
position. -/
abbrev statement : Prop :=
  ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      (∀ i : Fin n₁, u i ≠ 0) →
      (∀ j : Fin n₂, w j ≠ 0) →
      CoordinateUniform w →
      ∃ z : Fin k → ℂ, IsPhase z ∧
        (∀ (i : Fin n₁) (j : Fin n₂), pair (u i) (scale z w j) ≠ 0) ∧
        Transversal u (scale z w)

theorem target : statement := sorry

end Statements.UniformSecondBlockPlacement
