import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Basic
/-!
# Deliberately weakened control for `WeilSplitIsotropic` — expected RED

This is an honesty gate, not a claim.  It is the canonical proposition with the second
component of van Geemen's hermitian form **deleted** from Part A's conclusion: it proves only
`E x y = 0` on `W`, which is a hypothesis, and omits `E x (f y) = 0`, which is the whole
point.  Part B is likewise trimmed to its first three clauses.

The proposition below is strictly weaker than the canonical one, so
`example : Statements.WeilSplitIsotropic.statement := @…Weak.proof` must fail to elaborate.
Expected verdict: red, reason `restatement`.  If this ever comes back green, the
anti-restatement check is broken and the green sibling artifact must not be believed.
-/

set_option maxRecDepth 100000

namespace Submissions.WeilSplitIsotropic.Weak

open Finset

abbrev Idx (n : ℕ) : Type := Fin 4 × Fin n

def blk {n : ℕ} (A : Fin 4 → Fin 4 → ℤ) : Idx n → Idx n → ℤ :=
  fun x y => if x.2 = y.2 then A x.1 y.1 else 0

def Eb : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, -1, 0, 0]]

def Fb (d : ℤ) : Fin 4 → Fin 4 → ℤ := ![![0, -d, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, d, 0]]

def mul {n : ℕ} (A B : Idx n → Idx n → ℤ) : Idx n → Idx n → ℤ :=
  fun x z => ∑ y : Idx n, A x y * B y z

def tr {n : ℕ} (A : Idx n → Idx n → ℤ) : Idx n → Idx n → ℤ := fun x y => A y x

/-- The weakened proposition: Part A concludes only the isotropy it was handed, and Part B
keeps only the cheap clauses. -/
abbrev statement : Prop :=
  (∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (E : V →ₗ[R] V →ₗ[R] R) (f : V →ₗ[R] V) (d : R) (W : Submodule R V),
      (∀ x : V, E x x = 0) →
      (∀ x : V, f (f x) = -(d • x)) →
      (∀ x y : V, E (f x) (f y) = d * E x y) →
      (∀ w ∈ W, f w ∈ W) →
      (∀ x ∈ W, ∀ y ∈ W, E x y = 0) →
      ∀ x ∈ W, ∀ y ∈ W, E x y = 0)
  ∧
  (∀ (n : ℕ) (_d : ℤ),
      Fintype.card (Idx n) = 4 * n
    ∧ (∀ x y : Idx n, blk Eb x y = - blk Eb y x))

theorem proof : statement := by
  refine ⟨?_, ?_⟩
  · intro R _ V _ _ E f d W _halt _hsq _hsim _hstab hiso x hx y hy
    exact hiso x hx y hy
  · intro n _d
    refine ⟨by simp, ?_⟩
    intro x y
    have hEb : ∀ a c : Fin 4, Eb a c = - Eb c a := by decide
    simp only [blk]
    by_cases h : x.2 = y.2
    · simp [h, hEb x.1 y.1]
    · simp [h, Ne.symm h]

end Submissions.WeilSplitIsotropic.Weak
