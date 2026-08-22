import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# PhasePlacementUniform — separately achievable phase conditions are simultaneously achievable

Convention (as in `SpanningOrthRep4C10`, `CopiesTransversalCore`, the opposite of
Lovász–Saks–Schrijver): an edge of the orthogonality graph means the two vectors *are* orthogonal.

Context. `CopiesTransversalCore` (jig.so/p/14?s=15) proved the deterministic half of the copies
argument: if two blocks are each tight and `(k+1)`-spanning, have no cross orthogonality, and are
transversal — the span of a piece of each is as large as the two pieces' own ranks permit — then
their union is again tight and `(k+1)`-spanning. What remains is the existence of a placement with
those two cross properties, and that is the genericity half.

The usual route is Zariski density in the unitary group, which needs a rational parametrization of
`U(k)`. The cheaper route: a *diagonal phase* placement, `w j r ↦ z r * w j r` with every
`‖z r‖ = 1`, preserves the Hermitian pairing inside the second block exactly, so it preserves that
block's orthogonality graph, tightness and spanning identically. Only the cross conditions move,
and each is a polynomial in the phases — the cross pairings are linear forms in `z`, and each
transversality rank condition is a nonvanishing minor, whose Laplace expansion is a polynomial in
`z`. Combined with `TorusNonvanishing` (jig.so/p/14?s=20), which says finitely many nonzero
polynomials are simultaneously nonvanishing somewhere on the torus, this upgrades *separate*
achievability to *simultaneous* achievability, which is exactly what the deterministic half
consumes.

That upgrade is the statement below, and it is the whole genericity content in checkable form: the
hypotheses ask only that each single condition be achievable by *some* phase vector, one condition
at a time and with no coherence between the choices, and the conclusion produces one phase vector
that satisfies all of them at once.

The hypotheses are not vacuous and not automatic. A cross pairing between two vectors of *disjoint
support* vanishes for every phase vector, so a seed containing coordinate vectors — Chen–Johnston's
does — fails the first hypothesis until a fixed unitary is applied first to make the supports full;
that fixed change of basis is outside this statement.

Scope. Nothing is claimed about which seeds satisfy the hypotheses, about the fixed unitary that
may be needed to arrange them, about placements that are not diagonal phase maps, or about `k = 1`.
-/

namespace Statements.PhasePlacementUniform

variable {k : ℕ}

/-- The Hermitian pairing on `Fin k → ℂ`, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The rank of the subfamily of `v` indexed by a finite set `S`: the dimension of its span. -/
noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

/-- A phase vector: every coordinate has modulus one. Multiplying coordinatewise by such a vector
is a unitary map, so it preserves every Hermitian pairing within a block. -/
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

Fix a dimension `k ≥ 2` and two families `u`, `w` in `C^k`. Suppose each cross pair can be made
non-orthogonal by *some* phase vector, and each pair of subfamilies can be put in transversal
position by *some* phase vector — separately, with the choices unrelated. Then a single phase
vector does all of it at once: no cross orthogonality, and transversality for every pair of
subfamilies simultaneously. -/
abbrev statement : Prop :=
  ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      (∀ (i : Fin n₁) (j : Fin n₂),
        ∃ z : Fin k → ℂ, IsPhase z ∧ pair (u i) (scale z w j) ≠ 0) →
      (∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
        ∃ z : Fin k → ℂ, IsPhase z ∧
          rk (Sum.elim u (scale z w)) (S.disjSum T) = min k (rk u S + rk w T)) →
      ∃ z : Fin k → ℂ, IsPhase z ∧
        (∀ (i : Fin n₁) (j : Fin n₂), pair (u i) (scale z w j) ≠ 0) ∧
        Transversal u (scale z w)

theorem target : statement := sorry

end Statements.PhasePlacementUniform
