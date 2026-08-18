import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Basic
/-!
# Proof of `WeilSplitIsotropic`

**Part A** is one line: `f y ∈ W` because `W` is `f`-stable, and `W` is `E`-isotropic, so both
`E x y` and `E x (f y)` vanish.  The alternating, `f² = -d` and similitude hypotheses are
carried and unused; they say which situation the lemma is about, namely van Geemen's
(LNM 1594, Lemma 5.2).

**Part B** reduces every `4n × 4n` identity to a `4 × 4` one.  Both `E` and `f` have the form
`A ⊗ Iₙ` (`blk A` below), and `blk` is multiplicative — `(A ⊗ Iₙ)(B ⊗ Iₙ) = (AB) ⊗ Iₙ`
(`mul_blk`) and `(A ⊗ Iₙ)ᵀ = Aᵀ ⊗ Iₙ` (`tr_blk`) — so after those two lemmas every remaining
goal is about `Fin 4 → Fin 4 → ℤ`.  Nothing in the argument depends on `n`; `n` never appears
again after `mul_blk`.

The parameter-free `4 × 4` facts go by `decide`.  The four that carry `d` go by case analysis
on both indices, substituting numeral literals (`fin4`) rather than `fin_cases`: `fin_cases`
produces indices of the form `⟨k, _⟩`, on which the `Matrix.cons_val` dsimproc does not fire,
which forces the full `simp` set and costs about 350× more time.
-/

set_option maxRecDepth 100000

namespace Submissions.WeilSplitIsotropic.Split

open Finset

/-- Basis index for `H₁ = Γ₁ ⊕ Γ₂`: block, then position inside the block. -/
abbrev Idx (n : ℕ) : Type := Fin 4 × Fin n

/-- `blk A = A ⊗ Iₙ`. -/
def blk {n : ℕ} (A : Fin 4 → Fin 4 → ℤ) : Idx n → Idx n → ℤ :=
  fun x y => if x.2 = y.2 then A x.1 y.1 else 0

/-- The principal polarisation, block pattern. -/
def Eb : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, -1, 0, 0]]

/-- The action of `√-d`, block pattern. -/
def Fb (d : ℤ) : Fin 4 → Fin 4 → ℤ := ![![0, -d, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, d, 0]]

/-- Matrix product on `Idx n`. -/
def mul {n : ℕ} (A B : Idx n → Idx n → ℤ) : Idx n → Idx n → ℤ :=
  fun x z => ∑ y : Idx n, A x y * B y z

/-- Transpose. -/
def tr {n : ℕ} (A : Idx n → Idx n → ℤ) : Idx n → Idx n → ℤ := fun x y => A y x

/-- The proposition being claimed; a verbatim restatement of the canonical one. -/
abbrev statement : Prop :=
  (∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (E : V →ₗ[R] V →ₗ[R] R) (f : V →ₗ[R] V) (d : R) (W : Submodule R V),
      (∀ x : V, E x x = 0) →
      (∀ x : V, f (f x) = -(d • x)) →
      (∀ x y : V, E (f x) (f y) = d * E x y) →
      (∀ w ∈ W, f w ∈ W) →
      (∀ x ∈ W, ∀ y ∈ W, E x y = 0) →
      ∀ x ∈ W, ∀ y ∈ W, E x y = 0 ∧ E x (f y) = 0)
  ∧
  (∀ (n : ℕ) (d : ℤ),
      Fintype.card (Idx n) = 4 * n
    ∧ (∀ x y : Idx n, blk Eb x y = - blk Eb y x)
    ∧ (∀ x y : Idx n, mul (blk Eb) (blk Eb) x y = if x = y then -1 else 0)
    ∧ (∀ x y : Idx n, mul (blk (Fb d)) (blk (Fb d)) x y = if x = y then -d else 0)
    ∧ (∀ x y : Idx n, mul (tr (blk (Fb d))) (mul (blk Eb) (blk (Fb d))) x y = d * blk Eb x y)
    ∧ (∀ x y : Idx n, 2 ≤ (x.1 : ℕ) → 2 ≤ (y.1 : ℕ) → blk Eb x y = 0)
    ∧ (∀ x y : Idx n, 2 ≤ (y.1 : ℕ) → (x.1 : ℕ) < 2 → blk (Fb d) x y = 0)
    ∧ (∀ x y : Idx n, 2 ≤ (x.1 : ℕ) → 2 ≤ (y.1 : ℕ) → mul (blk Eb) (blk (Fb d)) x y = 0))

/-! ### Part A: the dimension-free lemma -/

theorem partA :
    ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (E : V →ₗ[R] V →ₗ[R] R) (f : V →ₗ[R] V) (d : R) (W : Submodule R V),
      (∀ x : V, E x x = 0) →
      (∀ x : V, f (f x) = -(d • x)) →
      (∀ x y : V, E (f x) (f y) = d * E x y) →
      (∀ w ∈ W, f w ∈ W) →
      (∀ x ∈ W, ∀ y ∈ W, E x y = 0) →
      ∀ x ∈ W, ∀ y ∈ W, E x y = 0 ∧ E x (f y) = 0 := by
  intro R _ V _ _ E f d W _halt _hsq _hsim hstab hiso x hx y hy
  exact ⟨hiso x hx y hy, hiso x hx (f y) (hstab y hy)⟩

/-! ### Part B, step 1: `blk` is a ring map, so `4n × 4n` collapses to `4 × 4` -/

/-- `4 × 4` matrix product. -/
def m4 (A B : Fin 4 → Fin 4 → ℤ) : Fin 4 → Fin 4 → ℤ := fun a c => ∑ b : Fin 4, A a b * B b c

/-- `(A ⊗ Iₙ)(B ⊗ Iₙ) = (AB) ⊗ Iₙ`. -/
theorem mul_blk {n : ℕ} (A B : Fin 4 → Fin 4 → ℤ) :
    mul (blk A) (blk B) = (blk (m4 A B) : Idx n → Idx n → ℤ) := by
  classical
  funext x z
  obtain ⟨a, i⟩ := x; obtain ⟨c, j⟩ := z
  simp only [mul, blk, m4, Fintype.sum_prod_type]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `(A ⊗ Iₙ)ᵀ = Aᵀ ⊗ Iₙ`. -/
theorem tr_blk {n : ℕ} (A : Fin 4 → Fin 4 → ℤ) :
    tr (blk A) = (blk (fun a b => A b a) : Idx n → Idx n → ℤ) := by
  funext x z
  obtain ⟨a, i⟩ := x; obtain ⟨c, j⟩ := z
  simp only [tr, blk]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Transport a `4 × 4` scalar-identity pattern through `blk`. -/
theorem blk_eq_ite {n : ℕ} (A : Fin 4 → Fin 4 → ℤ) (v : ℤ)
    (hA : ∀ a c : Fin 4, A a c = if a = c then v else 0) (x y : Idx n) :
    blk A x y = if x = y then v else 0 := by
  obtain ⟨a, i⟩ := x; obtain ⟨c, j⟩ := y
  simp only [blk, hA]
  by_cases h : i = j
  · subst h
    by_cases h2 : a = c
    · subst h2; simp
    · simp [h2, Prod.mk.injEq]
  · simp [h, Prod.mk.injEq]

/-- Transport a `4 × 4` vanishing pattern on the last two blocks through `blk`. -/
theorem blk_vanish {n : ℕ} (A : Fin 4 → Fin 4 → ℤ)
    (hA : ∀ a c : Fin 4, 2 ≤ (a : ℕ) → 2 ≤ (c : ℕ) → A a c = 0) (x y : Idx n)
    (hx : 2 ≤ (x.1 : ℕ)) (hy : 2 ≤ (y.1 : ℕ)) : blk A x y = 0 := by
  simp only [blk]
  by_cases h : x.2 = y.2
  · simp [h, hA _ _ hx hy]
  · simp [h]

/-! ### Part B, step 2: the `4 × 4` identities -/

theorem fin4 : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide

theorem eb_antisym : ∀ a c : Fin 4, Eb a c = - Eb c a := by decide

theorem m4_ee : ∀ a c : Fin 4, m4 Eb Eb a c = if a = c then -1 else 0 := by decide

theorem eb_g2 : ∀ a c : Fin 4, 2 ≤ (a : ℕ) → 2 ≤ (c : ℕ) → Eb a c = 0 := by decide

theorem m4_ff (d : ℤ) (a c : Fin 4) : m4 (Fb d) (Fb d) a c = if a = c then -d else 0 := by
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 c with rfl|rfl|rfl|rfl <;>
    simp only [m4, Fb, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue] <;>
    first | ring1 | simp | rfl

theorem m4_sim (d : ℤ) (a c : Fin 4) :
    m4 (fun p q => Fb d q p) (m4 Eb (Fb d)) a c = d * Eb a c := by
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 c with rfl|rfl|rfl|rfl <;>
    simp only [m4, Eb, Fb, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue] <;>
    first | ring1 | simp | rfl

theorem fb_g2 (d : ℤ) (a c : Fin 4) (hc : 2 ≤ (c : ℕ)) (ha : (a : ℕ) < 2) : Fb d a c = 0 := by
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 c with rfl|rfl|rfl|rfl <;>
    simp_all only [Fb, Matrix.cons_val, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] <;>
    first | rfl | omega

theorem m4_ef_g2 (d : ℤ) (a c : Fin 4) (ha : 2 ≤ (a : ℕ)) (hc : 2 ≤ (c : ℕ)) :
    m4 Eb (Fb d) a c = 0 := by
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 c with rfl|rfl|rfl|rfl <;>
    simp_all only [m4, Eb, Fb, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;> first | rfl | omega | ring1 | simp

/-! ### Assembly -/

theorem proof : statement := by
  refine ⟨partA, ?_⟩
  intro n d
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [blk]
    by_cases h : x.2 = y.2
    · simp [h, eb_antisym x.1 y.1]
    · simp [h, Ne.symm h]
  · intro x y
    rw [mul_blk]
    exact blk_eq_ite _ _ m4_ee x y
  · intro x y
    rw [mul_blk]
    exact blk_eq_ite _ _ (m4_ff d) x y
  · intro x y
    rw [tr_blk, mul_blk, mul_blk]
    simp only [blk]
    by_cases h : x.2 = y.2
    · simp [h, m4_sim d x.1 y.1]
    · simp [h]
  · intro x y hx hy
    exact blk_vanish _ eb_g2 x y hx hy
  · intro x y hy hx
    simp only [blk]
    by_cases h : x.2 = y.2
    · simp [h, fb_g2 d x.1 y.1 hy hx]
    · simp [h]
  · intro x y hx hy
    rw [mul_blk]
    exact blk_vanish _ (fun a c ha hc => m4_ef_g2 d a c ha hc) x y hx hy

end Submissions.WeilSplitIsotropic.Split
