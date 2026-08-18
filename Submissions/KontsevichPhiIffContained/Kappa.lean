import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Submissions.KontsevichPhiIffContained.Kappa

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open MvPolynomial

abbrev T : Type := MvPolynomial (Fin 10) ℚ

noncomputable def pv : Fin 4 → T := ![X 0, X 1, X 2, X 3]

noncomputable def bv : Fin 6 → T := ![X 4, X 5, X 6, X 7, X 8, X 9]

abbrev G2 : Type := Fin 4 → ℤ

abbrev Gp : Type := Fin 4 → ℤ

abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

def bivFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

def bivSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

def wedge (u v : G2) (k : Fin 6) : ℤ :=
  u (bivFst k) * v (bivSnd k) - u (bivSnd k) * v (bivFst k)

noncomputable def wedgePoly (u v : G2) : T := ∑ k : Fin 6, ((wedge u v k : ℤ) : ℚ) • bv k

noncomputable def parPoly (s : Gp) : T := ∑ k : Fin 4, ((s k : ℤ) : ℚ) • pv k

noncomputable def rowPoly (A : G2P) (i : Fin 4) : T := ∑ m : Fin 4, ((A i m : ℤ) : ℚ) • pv m

def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

noncomputable def app (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) : T :=
  ∑ k : Fin 6, ((β k : ℤ) : ℚ) • Φ x u k

noncomputable def triDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) (u - v) (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    + app Φ (x + outer v s) v (wedge u v)
    - app Φ (x + outer v s) (u - v) (wedge u v)
    - parPoly s ^ 2 * wedgePoly u v ^ 2

noncomputable def parDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s t : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) v (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    - app Φ (x + outer v t) u (wedge u v)
    + app Φ (x + outer v t) v (wedge u v)
    + app Φ (x + outer u s + outer v t) u (wedge u v)
    - app Φ (x + outer u s + outer v t) v (wedge u v)
    - (2 : ℚ) • (parPoly s * parPoly t * wedgePoly u v ^ 2)

/-- A triangle instance: vertex, parameter vector, two directions. -/
abbrev TriInst : Type := G2P × Gp × G2 × G2

/-- A parallelogram instance: vertex, two parameter vectors, two directions. -/
abbrev ParInst : Type := G2P × Gp × Gp × G2 × G2

/-- The `Φ`-side of Zharkov's triangle relation (1). -/
noncomputable def triPhi (Φ : G2P → G2 → Fin 6 → T) (e : TriInst) : T :=
  app Φ e.1 e.2.2.1 (wedge e.2.2.1 e.2.2.2) - app Φ e.1 e.2.2.2 (wedge e.2.2.1 e.2.2.2)
    + app Φ (e.1 + outer e.2.2.1 e.2.1) (e.2.2.1 - e.2.2.2) (wedge e.2.2.1 e.2.2.2)
    - app Φ (e.1 + outer e.2.2.1 e.2.1) e.2.2.1 (wedge e.2.2.1 e.2.2.2)
    + app Φ (e.1 + outer e.2.2.2 e.2.1) e.2.2.2 (wedge e.2.2.1 e.2.2.2)
    - app Φ (e.1 + outer e.2.2.2 e.2.1) (e.2.2.1 - e.2.2.2) (wedge e.2.2.1 e.2.2.2)

/-- The right-hand side of Zharkov's triangle relation (1): `s² ⊗ (u ∧ v)²`. -/
noncomputable def triRHS (e : TriInst) : T :=
  parPoly e.2.1 ^ 2 * wedgePoly e.2.2.1 e.2.2.2 ^ 2

/-- The `Φ`-side of Zharkov's parallelogram relation (2). -/
noncomputable def parPhi (Φ : G2P → G2 → Fin 6 → T) (e : ParInst) : T :=
  app Φ e.1 e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ e.1 e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
    + app Φ (e.1 + outer e.2.2.2.1 e.2.1) e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ (e.1 + outer e.2.2.2.1 e.2.1) e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ (e.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
    + app Φ (e.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
    + app Φ (e.1 + outer e.2.2.2.1 e.2.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.1
        (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ (e.1 + outer e.2.2.2.1 e.2.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.2
        (wedge e.2.2.2.1 e.2.2.2.2)

/-- The right-hand side of Zharkov's parallelogram relation (2): `2st ⊗ (u ∧ v)²`. -/
noncomputable def parRHS (e : ParInst) : T :=
  (2 : ℚ) • (parPoly e.2.1 * parPoly e.2.2.1 * wedgePoly e.2.2.2.1 e.2.2.2.2 ^ 2)

/-- One cell of a chain: a triangle or a parallelogram. -/
abbrev Cell : Type := TriInst ⊕ ParInst

/-- The `Φ`-side of a cell's relation. -/
noncomputable def cellPhi (Φ : G2P → G2 → Fin 6 → T) : Cell → T
  | Sum.inl e => triPhi Φ e
  | Sum.inr e => parPhi Φ e

/-- The tautological class of a cell: the right-hand side of its relation. -/
noncomputable def cellVol : Cell → T
  | Sum.inl e => triRHS e
  | Sum.inr e => parRHS e

/-- `u ∧ v` is a primitive vector of `⋀²Γ₂`. -/
def primBiv (u v : G2) : Prop := Finset.univ.gcd (wedge u v) = 1

/-- A cell is admissible when its two directions span a primitive bivector. -/
def cellPrim : Cell → Prop
  | Sum.inl e => primBiv e.2.2.1 e.2.2.2
  | Sum.inr e => primBiv e.2.2.2.1 e.2.2.2.2

/-- The defect of a cell's relation: the root statement's `triDefect` / `parDefect`. -/
noncomputable def cellDefect (Φ : G2P → G2 → Fin 6 → T) (z : Cell) : T :=
  cellPhi Φ z - cellVol z

/-- The four columns of Zharkov's polarisation matrix `Q`, read as elements of `Γ₂ ⊗ Γ_p`. -/
def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

/-- The period lattice `Γ₁ ⊆ Γ₂ ⊗ Γ_p`. -/
noncomputable def gammaOne (d : ℤ) : Submodule ℤ G2P :=
  Submodule.span ℤ (Set.range (gammaGen d))

/-- A family is *admissible* when it is `Γ₁`-periodic in the vertex and invariant under
nonzero integer rescaling of the direction — exactly the two side conditions the root
statement imposes on `Φ`. -/
def Admissible (d : ℤ) (Ψ : G2P → G2 → Fin 6 → T) : Prop :=
  (∀ (x : G2P) (u : G2) (g : G2P), g ∈ gammaOne d → Ψ (x + g) u = Ψ x u) ∧
    (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Ψ x (m • u) = Ψ x u)

/-- Completeness of the certificate (proved below as `completeness`). -/
abbrev completenessProp : Prop :=
  ∀ (d : ℤ) (L : Submodule ℤ T),
    (∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
        (∀ i ∈ s, cellPrim (z i)) →
        (∀ Ψ : G2P → G2 → Fin 6 → T, Admissible d Ψ →
            ∑ i ∈ s, (c i : T) * cellPhi Ψ (z i) = 0) →
        ∑ i ∈ s, (c i : T) * cellVol (z i) ∈ L) →
    ∃ Φ : G2P → G2 → Fin 6 → T, Admissible d Φ ∧
      ∀ z : Cell, cellPrim z → cellDefect Φ z ∈ L

/-! ## Index types -/

/-- Two directions are equivalent when they span the same rational line. -/
def lineRel (u v : G2) : Prop := ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ m • u = n • v

lemma lineRel_refl (u : G2) : lineRel u u := ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

lemma lineRel_symm {u v : G2} (h : lineRel u v) : lineRel v u := by
  obtain ⟨m, n, hm, hn, h⟩ := h; exact ⟨n, m, hn, hm, h.symm⟩

lemma lineRel_trans {u v w : G2} (h1 : lineRel u v) (h2 : lineRel v w) : lineRel u w := by
  obtain ⟨m, n, hm, hn, h1⟩ := h1
  obtain ⟨p, q, hp, hq, h2⟩ := h2
  refine ⟨p * m, n * q, mul_ne_zero hp hm, mul_ne_zero hn hq, ?_⟩
  calc (p * m) • u = p • (m • u) := by rw [mul_smul]
    _ = p • (n • v) := by rw [h1]
    _ = n • (p • v) := by rw [smul_comm]
    _ = n • (q • w) := by rw [h2]
    _ = (n * q) • w := by rw [mul_smul]

instance lineSetoid : Setoid G2 :=
  ⟨lineRel, ⟨lineRel_refl, fun h => lineRel_symm h, fun h1 h2 => lineRel_trans h1 h2⟩⟩

/-- Directions up to rescaling: `P(Γ₂ ⊗ ℚ)` together with `0`. -/
abbrev Line : Type := Quotient lineSetoid

/-- Vertices modulo the period lattice. -/
abbrev Vert (d : ℤ) : Type := G2P ⧸ gammaOne d

/-- The index set of an admissible family. -/
abbrev Idx (d : ℤ) : Type := Vert d × Line × Fin 6

/-- Rebuild a family from a function on the index set. -/
noncomputable def famOf (d : ℤ) (t : Idx d → T) : G2P → G2 → Fin 6 → T :=
  fun x u k => t (Submodule.Quotient.mk x, Quotient.mk _ u, k)

lemma famOf_admissible (d : ℤ) (t : Idx d → T) : Admissible d (famOf d t) := by
  constructor
  · intro x u g hg
    have : (Submodule.Quotient.mk (x + g) : Vert d) = Submodule.Quotient.mk x := by
      rw [Submodule.Quotient.eq]
      simpa using (gammaOne d).neg_mem hg
    funext k
    show t (Submodule.Quotient.mk (x + g), Quotient.mk _ u, k)
        = t (Submodule.Quotient.mk x, Quotient.mk _ u, k)
    rw [this]
  · intro x u m hm
    have hq : (Quotient.mk lineSetoid (m • u)) = Quotient.mk lineSetoid u :=
      Quotient.sound ⟨1, m, one_ne_zero, hm, by simp⟩
    funext k
    show t (Submodule.Quotient.mk x, Quotient.mk _ (m • u), k)
        = t (Submodule.Quotient.mk x, Quotient.mk _ u, k)
    rw [hq]

/-- Every admissible family is of that form. -/
noncomputable def funOf (d : ℤ) (Ψ : G2P → G2 → Fin 6 → T) : Idx d → T :=
  fun i => Ψ i.1.out i.2.1.out i.2.2

lemma famOf_funOf {d : ℤ} {Ψ : G2P → G2 → Fin 6 → T} (h : Admissible d Ψ) :
    famOf d (funOf d Ψ) = Ψ := by
  funext x u k
  show Ψ (Submodule.Quotient.mk x : Vert d).out (Quotient.mk lineSetoid u).out k = Ψ x u k
  have hx : Ψ (Submodule.Quotient.mk x : Vert d).out = Ψ x := by
    have hq : (Submodule.Quotient.mk (Submodule.Quotient.mk x : Vert d).out : Vert d)
        = Submodule.Quotient.mk x := Quotient.out_eq _
    rw [Submodule.Quotient.eq] at hq
    have hsplit : (Submodule.Quotient.mk x : Vert d).out
        = x + ((Submodule.Quotient.mk x : Vert d).out - x) := by abel
    rw [hsplit]
    funext u'
    exact h.1 x u' _ hq
  rw [hx]
  obtain ⟨m, n, hm, hn, hmn⟩ := Quotient.exact ((Quotient.out_eq (Quotient.mk lineSetoid u)))
  calc Ψ x (Quotient.mk lineSetoid u).out k
      = Ψ x (m • (Quotient.mk lineSetoid u).out) k := (congrFun (h.2 x _ m hm) k).symm
    _ = Ψ x (n • u) k := by rw [hmn]
    _ = Ψ x u k := congrFun (h.2 x u n hn) k

/-! ## The coefficient vector of a cell -/

/-- The index-space coefficient vector of one occurrence of `Φ_{x,u}(β)`. -/
noncomputable def sym (d : ℤ) (x : G2P) (u : G2) (β : Fin 6 → ℤ) : (Idx d) →₀ ℤ :=
  ∑ k : Fin 6, Finsupp.single ((Submodule.Quotient.mk x : Vert d), Quotient.mk _ u, k) (β k)

lemma pair_sym (d : ℤ) (t : Idx d → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) :
    Finsupp.linearCombination ℤ t (sym d x u β) = app (famOf d t) x u β := by
  simp only [sym, map_sum, Finsupp.linearCombination_single, app, famOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Int.cast_smul_eq_zsmul]

/-- The coefficient vector of a cell. -/
noncomputable def cellVec (d : ℤ) : Cell → (Idx d) →₀ ℤ
  | Sum.inl e =>
      sym d e.1 e.2.2.1 (wedge e.2.2.1 e.2.2.2) - sym d e.1 e.2.2.2 (wedge e.2.2.1 e.2.2.2)
        + sym d (e.1 + outer e.2.2.1 e.2.1) (e.2.2.1 - e.2.2.2) (wedge e.2.2.1 e.2.2.2)
        - sym d (e.1 + outer e.2.2.1 e.2.1) e.2.2.1 (wedge e.2.2.1 e.2.2.2)
        + sym d (e.1 + outer e.2.2.2 e.2.1) e.2.2.2 (wedge e.2.2.1 e.2.2.2)
        - sym d (e.1 + outer e.2.2.2 e.2.1) (e.2.2.1 - e.2.2.2) (wedge e.2.2.1 e.2.2.2)
  | Sum.inr e =>
      sym d e.1 e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
        - sym d e.1 e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
        + sym d (e.1 + outer e.2.2.2.1 e.2.1) e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
        - sym d (e.1 + outer e.2.2.2.1 e.2.1) e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
        - sym d (e.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
        + sym d (e.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
        + sym d (e.1 + outer e.2.2.2.1 e.2.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.1
            (wedge e.2.2.2.1 e.2.2.2.2)
        - sym d (e.1 + outer e.2.2.2.1 e.2.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.2
            (wedge e.2.2.2.1 e.2.2.2.2)

lemma pair_cellVec (d : ℤ) (t : Idx d → T) (z : Cell) :
    Finsupp.linearCombination ℤ t (cellVec d z) = cellPhi (famOf d t) z := by
  cases z with
  | inl e => simp only [cellVec, cellPhi, triPhi, map_add, map_sub, pair_sym]
  | inr e => simp only [cellVec, cellPhi, parPhi, map_add, map_sub, pair_sym]

/-! ## `T` and its quotients are divisible, hence Baer -/

noncomputable instance divisibleT : DivisibleBy T ℤ where
  div p n := ((n : ℚ))⁻¹ • p
  div_zero p := by simp
  div_cancel {n} p hn := by
    have hq : ((n : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_inv_cancel₀ hq, one_smul]

noncomputable instance divisibleQuot (L : Submodule ℤ T) : DivisibleBy (T ⧸ L) ℤ :=
  Function.Surjective.divisibleBy (L.mkQ.toAddMonoidHom) (Submodule.mkQ_surjective L)
    (fun a n => by
      show (Submodule.Quotient.mk (n • a) : T ⧸ L) = n • Submodule.Quotient.mk a
      exact Submodule.Quotient.mk_smul L n a)

/-! ## The main theorem -/

theorem completeness : completenessProp := by
  classical
  intro d L hyp
  set AC : Type := {z : Cell // cellPrim z} with hAC
  set EE : (AC →₀ ℤ) →ₗ[ℤ] ((Idx d) →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun z : AC => cellVec d z.1) with hEE
  set VV : (AC →₀ ℤ) →ₗ[ℤ] (T ⧸ L) :=
    Finsupp.linearCombination ℤ (fun z : AC => (Submodule.Quotient.mk (cellVol z.1) : T ⧸ L))
    with hVV
  have hker : LinearMap.ker EE ≤ LinearMap.ker VV := by
    intro a ha
    simp only [LinearMap.mem_ker] at ha ⊢
    have hbal : ∀ Ψ : G2P → G2 → Fin 6 → T, Admissible d Ψ →
        ∑ i ∈ a.support, ((a i : ℤ) : T) * cellPhi Ψ (i.1) = 0 := by
      intro Ψ hΨ
      have hrew : Ψ = famOf d (funOf d Ψ) := (famOf_funOf hΨ).symm
      set t := funOf d Ψ with ht
      have hEEa : EE a = ∑ i ∈ a.support, (a i) • cellVec d i.1 := by
        rw [hEE, Finsupp.linearCombination_apply, Finsupp.sum]
      have hmain : ∑ i ∈ a.support, ((a i : ℤ) : T) * cellPhi Ψ (i.1)
          = Finsupp.linearCombination ℤ t (EE a) := by
        rw [hrew, hEEa, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, pair_cellVec, zsmul_eq_mul]
      rw [hmain, ha, map_zero]
    have hcl := hyp AC a.support (fun i => a i) (fun i => i.1) (fun i _ => i.2) hbal
    rw [hVV, Finsupp.linearCombination_apply, Finsupp.sum]
    have hsum : ∑ i ∈ a.support, (a i) • (Submodule.Quotient.mk (cellVol i.1) : T ⧸ L)
        = L.mkQ (∑ i ∈ a.support, ((a i : ℤ) : T) * cellVol i.1) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.mkQ_apply, ← zsmul_eq_mul, Submodule.Quotient.mk_smul]
    rw [hsum]
    exact (Submodule.Quotient.mk_eq_zero L).mpr hcl
  set f' := Submodule.liftQ (LinearMap.ker EE) EE le_rfl with hf'
  set g' := Submodule.liftQ (LinearMap.ker EE) VV hker with hg'
  have hinj : Function.Injective f' :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  obtain ⟨H, hH⟩ := (Module.Baer.of_divisible (T ⧸ L)).extension_property f' hinj g'
  set rep : (T ⧸ L) → T := Function.surjInv (Submodule.mkQ_surjective L) with hrep
  have hrep_eq : ∀ q : T ⧸ L, (Submodule.Quotient.mk (rep q) : T ⧸ L) = q := by
    intro q
    exact Function.surjInv_eq (Submodule.mkQ_surjective L) q
  set t : Idx d → T := fun i => rep (H (Finsupp.single i 1)) with hts
  refine ⟨famOf d t, famOf_admissible d t, ?_⟩
  have hcomm : (L.mkQ).comp (Finsupp.linearCombination ℤ t) = H := by
    refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single,
      one_smul, Submodule.mkQ_apply, hts]
    exact hrep_eq _
  intro z hz
  have hEEz : EE (Finsupp.single (⟨z, hz⟩ : AC) 1) = cellVec d z := by
    rw [hEE, Finsupp.linearCombination_single, one_smul]
  have hVVz : VV (Finsupp.single (⟨z, hz⟩ : AC) 1) = Submodule.Quotient.mk (cellVol z) := by
    rw [hVV, Finsupp.linearCombination_single, one_smul]
  have key : (Submodule.Quotient.mk (cellPhi (famOf d t) z) : T ⧸ L)
      = Submodule.Quotient.mk (cellVol z) := by
    rw [← pair_cellVec d t z]
    have h1 : (Submodule.Quotient.mk (Finsupp.linearCombination ℤ t (cellVec d z)) : T ⧸ L)
        = H (cellVec d z) := by
      rw [← hcomm]; rfl
    rw [h1, ← hEEz]
    have h2 : EE (Finsupp.single (⟨z, hz⟩ : AC) 1)
        = f' (Submodule.Quotient.mk (Finsupp.single (⟨z, hz⟩ : AC) 1)) := by
      rw [hf', Submodule.liftQ_apply]
    rw [h2, ← LinearMap.comp_apply, hH, hg', Submodule.liftQ_apply, hVVz]
  rw [cellDefect, ← Submodule.Quotient.eq]
  exact key



/-! ## The root statement, restated verbatim -/

/-- The projection of `A ∧ B` to `Sym²Γ_p ⊗ ⋀²Γ₂`. -/
noncomputable def wedgeMat (A B : G2P) : T :=
  ∑ k : Fin 6,
    (rowPoly A (bivFst k) * rowPoly B (bivSnd k) - rowPoly A (bivSnd k) * rowPoly B (bivFst k))
      * bv k

/-- `θ`, the square of the polarisation. -/
noncomputable def theta (d : ℤ) : T :=
  ∑ k : Fin 6, wedgeMat (gammaGen d (bivFst k)) (gammaGen d (bivSnd k)) * bv k

/-- The first Weil class. -/
noncomputable def w1 (d : ℤ) : T :=
  let g := gammaGen d
  wedgeMat (g 0) (g 1) * bv 0
    - (1 / (d : ℚ)) • (wedgeMat (g 2) (g 3) * bv 0)
    - wedgeMat (g 0) (g 3) * bv 2
    + wedgeMat (g 0) (g 3) * bv 3
    + wedgeMat (g 1) (g 2) * bv 2
    - wedgeMat (g 1) (g 2) * bv 3
    - (d : ℚ) • (wedgeMat (g 0) (g 1) * bv 5)
    + wedgeMat (g 2) (g 3) * bv 5

/-- The second Weil class. -/
noncomputable def w2 (d : ℤ) : T :=
  let g := gammaGen d
  wedgeMat (g 0) (g 3) * bv 0
    - (d : ℚ) • (wedgeMat (g 0) (g 3) * bv 5)
    - (d : ℚ) • (wedgeMat (g 0) (g 1) * bv 3)
    + wedgeMat (g 2) (g 3) * bv 3
    + (d : ℚ) • (wedgeMat (g 0) (g 1) * bv 2)
    - wedgeMat (g 2) (g 3) * bv 2
    - wedgeMat (g 1) (g 2) * bv 0
    + (d : ℚ) • (wedgeMat (g 1) (g 2) * bv 5)

/-- The lattice `ℤ⟨θ, w₁, w₂⟩`. -/
noncomputable def weilLattice (d : ℤ) : Submodule ℤ T :=
  Submodule.span ℤ {theta d, w1 d, w2 d}

/-- The root statement of this problem, `KontsevichWeilPhi.statement`, restated verbatim. -/
abbrev rootProp : Prop :=
  ∃ d : ℤ, 0 < d ∧
    ∃ (L : Submodule ℤ T) (Φ : G2P → G2 → Fin 6 → T),
      L < weilLattice d ∧
      (∀ (x : G2P) (u : G2) (g : G2P), g ∈ gammaOne d → Φ (x + g) u = Φ x u) ∧
      (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Φ x (m • u) = Φ x u) ∧
      (∀ (x : G2P) (s : Gp) (u v : G2), primBiv u v → triDefect Φ x s u v ∈ L) ∧
      (∀ (x : G2P) (s t : Gp) (u v : G2), primBiv u v → parDefect Φ x s t u v ∈ L)

/-! ## The lattice of tautological classes -/

/-- The tautological class of a chain balanced over admissible families. -/
def chainClass (d : ℤ) : Set T :=
  { y | ∃ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
      (∀ i ∈ s, cellPrim (z i)) ∧
      (∀ Ψ : G2P → G2 → Fin 6 → T, Admissible d Ψ →
        ∑ i ∈ s, (c i : T) * cellPhi Ψ (z i) = 0) ∧
      y = ∑ i ∈ s, (c i : T) * cellVol (z i) }

/-- `Ξ_d`, the subgroup generated by those classes. -/
noncomputable def Xi (d : ℤ) : Submodule ℤ T := Submodule.span ℤ (chainClass d)

/-- The lattice form of the root question (proved equivalent below as `iffLattice`). -/
abbrev latticeProp : Prop :=
  rootProp ↔ ∃ d : ℤ, 0 < d ∧ Xi d < weilLattice d

theorem iffLattice : latticeProp := by
  constructor
  · rintro ⟨d, hd, L, Φ, hlt, hper, hsc, htri, hpar⟩
    refine ⟨d, hd, ?_⟩
    have hadm : Admissible d Φ := ⟨hper, hsc⟩
    have hdef : ∀ z : Cell, cellPrim z → cellDefect Φ z ∈ L := by
      rintro (e | e) hz
      · obtain ⟨x, s, u, v⟩ := e
        simpa [cellDefect, cellPhi, cellVol, triPhi, triRHS, triDefect] using htri x s u v hz
      · obtain ⟨x, s, t, u, v⟩ := e
        simpa [cellDefect, cellPhi, cellVol, parPhi, parRHS, parDefect] using hpar x s t u v hz
    have hsub : chainClass d ⊆ (L : Set T) := by
      rintro y ⟨ι, s, c, z, hprim, hbal, rfl⟩
      have h1 : ∑ i ∈ s, (c i : T) * cellDefect Φ (z i) ∈ L := by
        refine Submodule.sum_mem _ fun i hi => ?_
        simpa [zsmul_eq_mul] using L.smul_mem (c i) (hdef (z i) (hprim i hi))
      have h2 : ∑ i ∈ s, (c i : T) * cellDefect Φ (z i)
          = (∑ i ∈ s, (c i : T) * cellPhi Φ (z i)) - ∑ i ∈ s, (c i : T) * cellVol (z i) := by
        simp [cellDefect, mul_sub, Finset.sum_sub_distrib]
      rw [h2, hbal Φ hadm, zero_sub] at h1
      exact (Submodule.neg_mem_iff L).mp h1
    exact lt_of_le_of_lt (Submodule.span_le.mpr hsub) hlt
  · rintro ⟨d, hd, hlt⟩
    refine ⟨d, hd, Xi d, ?_⟩
    have hhyp : ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
        (∀ i ∈ s, cellPrim (z i)) →
        (∀ Ψ : G2P → G2 → Fin 6 → T, Admissible d Ψ →
            ∑ i ∈ s, (c i : T) * cellPhi Ψ (z i) = 0) →
        ∑ i ∈ s, (c i : T) * cellVol (z i) ∈ Xi d :=
      fun ι s c z hprim hbal => Submodule.subset_span ⟨ι, s, c, z, hprim, hbal, rfl⟩
    obtain ⟨Φ, hadm, hdef⟩ := completeness d (Xi d) hhyp
    refine ⟨Φ, hlt, hadm.1, hadm.2, ?_, ?_⟩
    · intro x s u v hp
      have h := hdef (Sum.inl (x, s, u, v)) hp
      simpa [cellDefect, cellPhi, cellVol, triPhi, triRHS, triDefect] using h
    · intro x s t u v hp
      have h := hdef (Sum.inr (x, s, t, u, v)) hp
      simpa [cellDefect, cellPhi, cellVol, parPhi, parRHS, parDefect] using h



/-! ## A parity functional -/

/-- The evaluation point `a = α, b = 0, c = γ, e = 0, x₁₂ = 1, every other bivector
coordinate `0`. -/
noncomputable def pt (al ga : ℚ) : Fin 10 → ℚ := ![al, 0, ga, 0, 1, 0, 0, 0, 0, 0]

/-- On a bidegree-`(2,2)` element this reads off the coefficient of `a·c·x₁₂²`. -/
noncomputable def kap (p : T) : ℚ :=
  eval (pt 1 1) p - eval (pt 1 0) p - eval (pt 0 1) p

lemma kap_add (p q : T) : kap (p + q) = kap p + kap q := by
  simp only [kap, map_add]; ring

lemma kap_zsmul (n : ℤ) (p : T) : kap (n • p) = (n : ℚ) * kap p := by
  simp only [kap, map_zsmul]; push_cast; ring

lemma eval_parPoly (al ga : ℚ) (s : Gp) :
    eval (pt al ga) (parPoly s) = (s 0 : ℚ) * al + (s 2 : ℚ) * ga := by
  simp [parPoly, pv, pt, Fin.sum_univ_four]

lemma eval_wedgePoly (al ga : ℚ) (u v : G2) :
    eval (pt al ga) (wedgePoly u v) = ((wedge u v 0 : ℤ) : ℚ) := by
  simp [wedgePoly, bv, pt, Fin.sum_univ_six]

lemma kap_theta (d : ℤ) : kap (theta d) = 1 := by
  have h : ∀ al ga : ℚ, eval (pt al ga) (theta d) = al * ga := by
    intro al ga
    simp [theta, wedgeMat, rowPoly, gammaGen, pv, bv, pt, Fin.sum_univ_six, Fin.sum_univ_four,
      bivFst, bivSnd]
  simp [kap, h]

lemma kap_cellVol (z : Cell) : ∃ m : ℤ, kap (cellVol z) = 2 * (m : ℚ) := by
  cases z with
  | inl e =>
    obtain ⟨x, s, u, v⟩ := e
    refine ⟨s 0 * s 2 * (wedge u v 0) ^ 2, ?_⟩
    simp only [cellVol, triRHS, kap, map_mul, map_pow, eval_parPoly, eval_wedgePoly]
    push_cast
    ring
  | inr e =>
    obtain ⟨x, s, t, u, v⟩ := e
    refine ⟨(s 0 * t 2 + s 2 * t 0) * (wedge u v 0) ^ 2, ?_⟩
    simp only [cellVol, parRHS, kap, smul_eq_C_mul, map_mul, map_pow, eval_C, eval_parPoly,
      eval_wedgePoly]
    push_cast
    ring

/-- The submodule on which `kap` is even. -/
noncomputable def evenKap : Submodule ℤ T where
  carrier := {p | ∃ m : ℤ, kap p = 2 * (m : ℚ)}
  add_mem' := by
    rintro p q ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by rw [kap_add, hm, hn]; push_cast; ring⟩
  zero_mem' := ⟨0, by simp [kap]⟩
  smul_mem' := by
    rintro n p ⟨m, hm⟩
    exact ⟨n * m, by rw [kap_zsmul, hm]; push_cast; ring⟩

lemma Xi_le_evenKap (d : ℤ) : Xi d ≤ evenKap := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨ι, s, c, z, hprim, hbal, rfl⟩
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨m, hm⟩ := kap_cellVol (z i)
  refine ⟨c i * m, ?_⟩
  have : ((c i : T)) * cellVol (z i) = (c i) • cellVol (z i) := by
    rw [zsmul_eq_mul]
  rw [this, kap_zsmul, hm]
  push_cast; ring

lemma theta_not_mem_Xi (d : ℤ) : theta d ∉ Xi d := by
  intro h
  obtain ⟨m, hm⟩ := Xi_le_evenKap d h
  rw [kap_theta] at hm
  have : (2 : ℚ) * (m : ℚ) = 1 := hm.symm
  have h2 : (2 * m : ℤ) = 1 := by exact_mod_cast this
  omega

/-- The canonical proposition.  This is the type the verifier demands. -/
abbrev statement : Prop :=
  rootProp ↔ ∃ d : ℤ, 0 < d ∧ Xi d ≤ weilLattice d

theorem proof : statement := by
  constructor
  · intro h
    obtain ⟨d, hd, hlt⟩ := iffLattice.mp h
    exact ⟨d, hd, le_of_lt hlt⟩
  · rintro ⟨d, hd, hle⟩
    refine iffLattice.mpr ⟨d, hd, lt_of_le_of_ne hle ?_⟩
    intro heq
    exact theta_not_mem_Xi d (heq ▸ (Submodule.subset_span (by simp)))

end Submissions.KontsevichPhiIffContained.Kappa
