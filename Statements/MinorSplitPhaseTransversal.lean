import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# MinorSplitPhaseTransversal — a finite minor condition suffices for a phase placement

Convention (as in `CopiesTransversalCore`, `PhasePlacementUniform`, the opposite of
Lovász–Saks–Schrijver): an edge of the orthogonality graph means the two vectors *are* orthogonal.

Context. `PhasePlacementUniform` (jig.so/p/14?s=22) upgrades separate achievability of the cross
conditions to simultaneous achievability, but its hypotheses are themselves existential over
phases — one still has to know that *some* phase puts a given pair of subfamilies in transversal
position. This statement discharges both hypotheses from data that is finite, checkable by exact
arithmetic on the two families, and free of any quantifier over phases.

The two conditions. For the cross pairings, `pair (u i) (scale z w j) = ∑ r, star (u i r) * z r *
w j r` is a linear form in `z`, and it is a *nonzero* linear form exactly when some coordinate
carries both vectors — that is the overlapping-support hypothesis, and no phase can help when it
fails. For transversality, expanding the relevant `t × t` determinant along the split between rows
taken from the first family and rows taken from the second groups the permutations by which columns
the second block occupies: the coefficient of the squarefree monomial `∏ r ∈ D, z r` is
`± det (first block on the complementary columns) * det (second block on D)`, and distinct column
sets `D` give distinct monomials. So a single split with both minors nonzero already makes the
determinant a nonzero polynomial, which is all that is needed.

Why the weak form is the right one. Total coordinate general position — every square minor of the
coefficient matrix nonzero — is *unavailable*, and not merely hard to find: in a `k`-regular
orthogonality graph the `k` neighbours of a vertex lie in that vertex's orthogonal complement, so
those `k` rows are dependent and their full-size minors vanish for every choice of coordinates,
being invariant under every invertible change of basis. The minor-split condition below asks only
for *one* good split per pair of subfamilies, which is compatible with those forced dependencies.

Scope. Only diagonal phase placements are considered. Nothing is claimed about which families
satisfy the hypotheses, about the fixed change of basis that may be needed to arrange them, or
about `k = 1`. The conclusion is the cross input of `CopiesTransversalCore`, not a gadget.
-/

namespace Statements.MinorSplitPhaseTransversal

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

/-- Transversality of two blocks: the span of a piece of each is as large as the two pieces' own
ranks permit. This is the hypothesis of `CopiesTransversalCore`. -/
abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) : Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

/-- The canonical proposition.

Fix `k ≥ 2` and two families `u`, `w` in `C^k`. Suppose

* every cross pair shares a coordinate on which both vectors are nonzero, and
* for every pair of subfamilies `S`, `T` there is a *split*: rows drawn from `S` and from `T`, in
  numbers adding up to the target rank `min k (rk u S + rk w T)`, together with *disjoint* column
  sets of the matching sizes, such that both square minors so formed are nonzero.

Then a single phase vector makes every cross pairing nonzero and puts the two families in
transversal position. -/
abbrev statement : Prop :=
  ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      (∀ (i : Fin n₁) (j : Fin n₂), ∃ r : Fin k, u i r ≠ 0 ∧ w j r ≠ 0) →
      (∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
        ∃ (ta tb : ℕ) (a : Fin ta → Fin n₁) (b : Fin tb → Fin n₂)
          (c : Fin ta → Fin k) (e : Fin tb → Fin k),
          ta + tb = min k (rk u S + rk w T) ∧
          (∀ p, a p ∈ S) ∧ (∀ q, b q ∈ T) ∧
          Function.Injective a ∧ Function.Injective b ∧
          Function.Injective c ∧ Function.Injective e ∧
          (∀ p q, c p ≠ e q) ∧
          Matrix.det (Matrix.of fun p q => u (a p) (c q)) ≠ 0 ∧
          Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0) →
      ∃ z : Fin k → ℂ, IsPhase z ∧
        (∀ (i : Fin n₁) (j : Fin n₂), pair (u i) (scale z w j) ≠ 0) ∧
        Transversal u (scale z w)

theorem target : statement := sorry

end Statements.MinorSplitPhaseTransversal
