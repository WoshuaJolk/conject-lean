import Mathlib

/-! # Symmetry + Plücker cut `⋀²Γ₁ ⊗ ⋀²Γ₂` down to `ℤ⟨θ, w₁, w₂⟩` at `d = 1` -/

namespace Submissions.GammaOneSymPluckerLattice.Lat

open MvPolynomial

noncomputable section

abbrev T : Type := MvPolynomial (Fin 10) ℚ
noncomputable def pv : Fin 4 → T := ![X 0, X 1, X 2, X 3]
noncomputable def bv : Fin 6 → T := ![X 4, X 5, X 6, X 7, X 8, X 9]
abbrev G2 : Type := Fin 4 → ℤ
abbrev Gp : Type := Fin 4 → ℤ
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ
def bivFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def bivSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]
noncomputable def rowPoly (A : G2P) (i : Fin 4) : T := ∑ m : Fin 4, ((A i m : ℤ) : ℚ) • pv m
noncomputable def wedgeMat (A B : G2P) : T :=
  ∑ k : Fin 6,
    (rowPoly A (bivFst k) * rowPoly B (bivSnd k) - rowPoly A (bivSnd k) * rowPoly B (bivFst k))
      * bv k
def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]
noncomputable def wcoef (d : ℤ) (j l : Fin 6) : T :=
  rowPoly (gammaGen d (bivFst j)) (bivFst l) * rowPoly (gammaGen d (bivSnd j)) (bivSnd l)
    - rowPoly (gammaGen d (bivFst j)) (bivSnd l) * rowPoly (gammaGen d (bivSnd j)) (bivFst l)
noncomputable def gm (d : ℤ) (j : Fin 6) : T :=
  wedgeMat (gammaGen d (bivFst j)) (gammaGen d (bivSnd j))
noncomputable def theta (d : ℤ) : T :=
  ∑ k : Fin 6, wedgeMat (gammaGen d (bivFst k)) (gammaGen d (bivSnd k)) * bv k
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
noncomputable def weilLattice (d : ℤ) : Submodule ℤ T :=
  Submodule.span ℤ {theta d, w1 d, w2 d}

/-! ### Integer evaluation of the parameters -/

noncomputable def ep (p : Fin 4 → ℤ) : T →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval ![((p 0 : ℤ) : ℚ), ((p 1 : ℤ) : ℚ), ((p 2 : ℤ) : ℚ), ((p 3 : ℤ) : ℚ),
    0, 0, 0, 0, 0, 0]

def rz (A : G2P) (i : Fin 4) (p : Fin 4 → ℤ) : ℤ :=
  A i 0 * p 0 + A i 1 * p 1 + A i 2 * p 2 + A i 3 * p 3

def wcz (p : Fin 4 → ℤ) (j l : Fin 6) : ℤ :=
  rz (gammaGen 1 (bivFst j)) (bivFst l) p * rz (gammaGen 1 (bivSnd j)) (bivSnd l) p
    - rz (gammaGen 1 (bivFst j)) (bivSnd l) p * rz (gammaGen 1 (bivSnd j)) (bivFst l) p

lemma ep_pv (p : Fin 4 → ℤ) (l : Fin 4) : ep p (pv l) = ((p l : ℤ) : ℚ) := by
  fin_cases l <;> simp [ep, pv]

lemma ep_rowPoly (p : Fin 4 → ℤ) (A : G2P) (i : Fin 4) :
    ep p (rowPoly A i) = ((rz A i p : ℤ) : ℚ) := by
  rw [rowPoly, map_sum, Fin.sum_univ_four]
  simp only [map_smul, smul_eq_mul, ep_pv, rz]
  push_cast
  ring

lemma ep_wcoef (p : Fin 4 → ℤ) (j l : Fin 6) :
    ep p (wcoef 1 j l) = ((wcz p j l : ℤ) : ℚ) := by
  simp only [wcoef, wcz, map_sub, map_mul, ep_rowPoly]
  push_cast
  ring

/-! ### The four evaluation points and the value table -/

def P0 : Fin 4 → ℤ := ![1, 0, 0, 0]
def P1 : Fin 4 → ℤ := ![0, 1, 0, 0]
def P2 : Fin 4 → ℤ := ![0, 0, 1, 0]
def P3 : Fin 4 → ℤ := ![1, 0, 0, 1]

@[simp] lemma wz0_0_0 : wcz P0 0 0 = 0 := by decide
@[simp] lemma wz0_0_1 : wcz P0 0 1 = 0 := by decide
@[simp] lemma wz0_0_2 : wcz P0 0 2 = 0 := by decide
@[simp] lemma wz0_0_3 : wcz P0 0 3 = 0 := by decide
@[simp] lemma wz0_0_4 : wcz P0 0 4 = 0 := by decide
@[simp] lemma wz0_0_5 : wcz P0 0 5 = 0 := by decide
@[simp] lemma wz0_1_0 : wcz P0 1 0 = 0 := by decide
@[simp] lemma wz0_1_1 : wcz P0 1 1 = 1 := by decide
@[simp] lemma wz0_1_2 : wcz P0 1 2 = 0 := by decide
@[simp] lemma wz0_1_3 : wcz P0 1 3 = 0 := by decide
@[simp] lemma wz0_1_4 : wcz P0 1 4 = 0 := by decide
@[simp] lemma wz0_1_5 : wcz P0 1 5 = 0 := by decide
@[simp] lemma wz0_2_0 : wcz P0 2 0 = 0 := by decide
@[simp] lemma wz0_2_1 : wcz P0 2 1 = 0 := by decide
@[simp] lemma wz0_2_2 : wcz P0 2 2 = 0 := by decide
@[simp] lemma wz0_2_3 : wcz P0 2 3 = 0 := by decide
@[simp] lemma wz0_2_4 : wcz P0 2 4 = 0 := by decide
@[simp] lemma wz0_2_5 : wcz P0 2 5 = 0 := by decide
@[simp] lemma wz0_3_0 : wcz P0 3 0 = 0 := by decide
@[simp] lemma wz0_3_1 : wcz P0 3 1 = 0 := by decide
@[simp] lemma wz0_3_2 : wcz P0 3 2 = 0 := by decide
@[simp] lemma wz0_3_3 : wcz P0 3 3 = 0 := by decide
@[simp] lemma wz0_3_4 : wcz P0 3 4 = 0 := by decide
@[simp] lemma wz0_3_5 : wcz P0 3 5 = 0 := by decide
@[simp] lemma wz0_4_0 : wcz P0 4 0 = 0 := by decide
@[simp] lemma wz0_4_1 : wcz P0 4 1 = 0 := by decide
@[simp] lemma wz0_4_2 : wcz P0 4 2 = 0 := by decide
@[simp] lemma wz0_4_3 : wcz P0 4 3 = 0 := by decide
@[simp] lemma wz0_4_4 : wcz P0 4 4 = 0 := by decide
@[simp] lemma wz0_4_5 : wcz P0 4 5 = 0 := by decide
@[simp] lemma wz0_5_0 : wcz P0 5 0 = 0 := by decide
@[simp] lemma wz0_5_1 : wcz P0 5 1 = 0 := by decide
@[simp] lemma wz0_5_2 : wcz P0 5 2 = 0 := by decide
@[simp] lemma wz0_5_3 : wcz P0 5 3 = 0 := by decide
@[simp] lemma wz0_5_4 : wcz P0 5 4 = 0 := by decide
@[simp] lemma wz0_5_5 : wcz P0 5 5 = 0 := by decide
@[simp] lemma wz1_0_0 : wcz P1 0 0 = -1 := by decide
@[simp] lemma wz1_0_1 : wcz P1 0 1 = 0 := by decide
@[simp] lemma wz1_0_2 : wcz P1 0 2 = 0 := by decide
@[simp] lemma wz1_0_3 : wcz P1 0 3 = 0 := by decide
@[simp] lemma wz1_0_4 : wcz P1 0 4 = 0 := by decide
@[simp] lemma wz1_0_5 : wcz P1 0 5 = 0 := by decide
@[simp] lemma wz1_1_0 : wcz P1 1 0 = 0 := by decide
@[simp] lemma wz1_1_1 : wcz P1 1 1 = 0 := by decide
@[simp] lemma wz1_1_2 : wcz P1 1 2 = 0 := by decide
@[simp] lemma wz1_1_3 : wcz P1 1 3 = 0 := by decide
@[simp] lemma wz1_1_4 : wcz P1 1 4 = 1 := by decide
@[simp] lemma wz1_1_5 : wcz P1 1 5 = 0 := by decide
@[simp] lemma wz1_2_0 : wcz P1 2 0 = 0 := by decide
@[simp] lemma wz1_2_1 : wcz P1 2 1 = 0 := by decide
@[simp] lemma wz1_2_2 : wcz P1 2 2 = 0 := by decide
@[simp] lemma wz1_2_3 : wcz P1 2 3 = 1 := by decide
@[simp] lemma wz1_2_4 : wcz P1 2 4 = 0 := by decide
@[simp] lemma wz1_2_5 : wcz P1 2 5 = 0 := by decide
@[simp] lemma wz1_3_0 : wcz P1 3 0 = 0 := by decide
@[simp] lemma wz1_3_1 : wcz P1 3 1 = 0 := by decide
@[simp] lemma wz1_3_2 : wcz P1 3 2 = 1 := by decide
@[simp] lemma wz1_3_3 : wcz P1 3 3 = 0 := by decide
@[simp] lemma wz1_3_4 : wcz P1 3 4 = 0 := by decide
@[simp] lemma wz1_3_5 : wcz P1 3 5 = 0 := by decide
@[simp] lemma wz1_4_0 : wcz P1 4 0 = 0 := by decide
@[simp] lemma wz1_4_1 : wcz P1 4 1 = 1 := by decide
@[simp] lemma wz1_4_2 : wcz P1 4 2 = 0 := by decide
@[simp] lemma wz1_4_3 : wcz P1 4 3 = 0 := by decide
@[simp] lemma wz1_4_4 : wcz P1 4 4 = 0 := by decide
@[simp] lemma wz1_4_5 : wcz P1 4 5 = 0 := by decide
@[simp] lemma wz1_5_0 : wcz P1 5 0 = 0 := by decide
@[simp] lemma wz1_5_1 : wcz P1 5 1 = 0 := by decide
@[simp] lemma wz1_5_2 : wcz P1 5 2 = 0 := by decide
@[simp] lemma wz1_5_3 : wcz P1 5 3 = 0 := by decide
@[simp] lemma wz1_5_4 : wcz P1 5 4 = 0 := by decide
@[simp] lemma wz1_5_5 : wcz P1 5 5 = -1 := by decide
@[simp] lemma wz2_0_0 : wcz P2 0 0 = 0 := by decide
@[simp] lemma wz2_0_1 : wcz P2 0 1 = 0 := by decide
@[simp] lemma wz2_0_2 : wcz P2 0 2 = 0 := by decide
@[simp] lemma wz2_0_3 : wcz P2 0 3 = 0 := by decide
@[simp] lemma wz2_0_4 : wcz P2 0 4 = 0 := by decide
@[simp] lemma wz2_0_5 : wcz P2 0 5 = 0 := by decide
@[simp] lemma wz2_1_0 : wcz P2 1 0 = 0 := by decide
@[simp] lemma wz2_1_1 : wcz P2 1 1 = 0 := by decide
@[simp] lemma wz2_1_2 : wcz P2 1 2 = 0 := by decide
@[simp] lemma wz2_1_3 : wcz P2 1 3 = 0 := by decide
@[simp] lemma wz2_1_4 : wcz P2 1 4 = 0 := by decide
@[simp] lemma wz2_1_5 : wcz P2 1 5 = 0 := by decide
@[simp] lemma wz2_2_0 : wcz P2 2 0 = 0 := by decide
@[simp] lemma wz2_2_1 : wcz P2 2 1 = 0 := by decide
@[simp] lemma wz2_2_2 : wcz P2 2 2 = 0 := by decide
@[simp] lemma wz2_2_3 : wcz P2 2 3 = 0 := by decide
@[simp] lemma wz2_2_4 : wcz P2 2 4 = 0 := by decide
@[simp] lemma wz2_2_5 : wcz P2 2 5 = 0 := by decide
@[simp] lemma wz2_3_0 : wcz P2 3 0 = 0 := by decide
@[simp] lemma wz2_3_1 : wcz P2 3 1 = 0 := by decide
@[simp] lemma wz2_3_2 : wcz P2 3 2 = 0 := by decide
@[simp] lemma wz2_3_3 : wcz P2 3 3 = 0 := by decide
@[simp] lemma wz2_3_4 : wcz P2 3 4 = 0 := by decide
@[simp] lemma wz2_3_5 : wcz P2 3 5 = 0 := by decide
@[simp] lemma wz2_4_0 : wcz P2 4 0 = 0 := by decide
@[simp] lemma wz2_4_1 : wcz P2 4 1 = 0 := by decide
@[simp] lemma wz2_4_2 : wcz P2 4 2 = 0 := by decide
@[simp] lemma wz2_4_3 : wcz P2 4 3 = 0 := by decide
@[simp] lemma wz2_4_4 : wcz P2 4 4 = 1 := by decide
@[simp] lemma wz2_4_5 : wcz P2 4 5 = 0 := by decide
@[simp] lemma wz2_5_0 : wcz P2 5 0 = 0 := by decide
@[simp] lemma wz2_5_1 : wcz P2 5 1 = 0 := by decide
@[simp] lemma wz2_5_2 : wcz P2 5 2 = 0 := by decide
@[simp] lemma wz2_5_3 : wcz P2 5 3 = 0 := by decide
@[simp] lemma wz2_5_4 : wcz P2 5 4 = 0 := by decide
@[simp] lemma wz2_5_5 : wcz P2 5 5 = 0 := by decide
@[simp] lemma wz3_0_0 : wcz P3 0 0 = 0 := by decide
@[simp] lemma wz3_0_1 : wcz P3 0 1 = -1 := by decide
@[simp] lemma wz3_0_2 : wcz P3 0 2 = 0 := by decide
@[simp] lemma wz3_0_3 : wcz P3 0 3 = 0 := by decide
@[simp] lemma wz3_0_4 : wcz P3 0 4 = 0 := by decide
@[simp] lemma wz3_0_5 : wcz P3 0 5 = 1 := by decide
@[simp] lemma wz3_1_0 : wcz P3 1 0 = -1 := by decide
@[simp] lemma wz3_1_1 : wcz P3 1 1 = 1 := by decide
@[simp] lemma wz3_1_2 : wcz P3 1 2 = 0 := by decide
@[simp] lemma wz3_1_3 : wcz P3 1 3 = 0 := by decide
@[simp] lemma wz3_1_4 : wcz P3 1 4 = 1 := by decide
@[simp] lemma wz3_1_5 : wcz P3 1 5 = -1 := by decide
@[simp] lemma wz3_2_0 : wcz P3 2 0 = 0 := by decide
@[simp] lemma wz3_2_1 : wcz P3 2 1 = 0 := by decide
@[simp] lemma wz3_2_2 : wcz P3 2 2 = -1 := by decide
@[simp] lemma wz3_2_3 : wcz P3 2 3 = 0 := by decide
@[simp] lemma wz3_2_4 : wcz P3 2 4 = 0 := by decide
@[simp] lemma wz3_2_5 : wcz P3 2 5 = 0 := by decide
@[simp] lemma wz3_3_0 : wcz P3 3 0 = 0 := by decide
@[simp] lemma wz3_3_1 : wcz P3 3 1 = 0 := by decide
@[simp] lemma wz3_3_2 : wcz P3 3 2 = 0 := by decide
@[simp] lemma wz3_3_3 : wcz P3 3 3 = -1 := by decide
@[simp] lemma wz3_3_4 : wcz P3 3 4 = 0 := by decide
@[simp] lemma wz3_3_5 : wcz P3 3 5 = 0 := by decide
@[simp] lemma wz3_4_0 : wcz P3 4 0 = 0 := by decide
@[simp] lemma wz3_4_1 : wcz P3 4 1 = 1 := by decide
@[simp] lemma wz3_4_2 : wcz P3 4 2 = 0 := by decide
@[simp] lemma wz3_4_3 : wcz P3 4 3 = 0 := by decide
@[simp] lemma wz3_4_4 : wcz P3 4 4 = 0 := by decide
@[simp] lemma wz3_4_5 : wcz P3 4 5 = 0 := by decide
@[simp] lemma wz3_5_0 : wcz P3 5 0 = 1 := by decide
@[simp] lemma wz3_5_1 : wcz P3 5 1 = -1 := by decide
@[simp] lemma wz3_5_2 : wcz P3 5 2 = 0 := by decide
@[simp] lemma wz3_5_3 : wcz P3 5 3 = 0 := by decide
@[simp] lemma wz3_5_4 : wcz P3 5 4 = 0 := by decide
@[simp] lemma wz3_5_5 : wcz P3 5 5 = 0 := by decide

/-! ### The three named solutions -/

lemma gm_eq (j : Fin 6) : gm 1 j = ∑ l : Fin 6, wcoef 1 j l * bv l := rfl

lemma gmv0 : gm 1 0 = wedgeMat (gammaGen 1 0) (gammaGen 1 1) := rfl
lemma gmv1 : gm 1 1 = wedgeMat (gammaGen 1 0) (gammaGen 1 2) := rfl
lemma gmv2 : gm 1 2 = wedgeMat (gammaGen 1 0) (gammaGen 1 3) := rfl
lemma gmv3 : gm 1 3 = wedgeMat (gammaGen 1 1) (gammaGen 1 2) := rfl
lemma gmv4 : gm 1 4 = wedgeMat (gammaGen 1 1) (gammaGen 1 3) := rfl
lemma gmv5 : gm 1 5 = wedgeMat (gammaGen 1 2) (gammaGen 1 3) := rfl

lemma theta_eq : theta 1 = wedgeMat (gammaGen 1 0) (gammaGen 1 1) * bv 0
    + wedgeMat (gammaGen 1 0) (gammaGen 1 2) * bv 1
    + wedgeMat (gammaGen 1 0) (gammaGen 1 3) * bv 2
    + wedgeMat (gammaGen 1 1) (gammaGen 1 2) * bv 3
    + wedgeMat (gammaGen 1 1) (gammaGen 1 3) * bv 4
    + wedgeMat (gammaGen 1 2) (gammaGen 1 3) * bv 5 := by
  rw [theta, Fin.sum_univ_six]
  rfl

lemma w1_eq : w1 1 = wedgeMat (gammaGen 1 0) (gammaGen 1 1) * bv 0
    - wedgeMat (gammaGen 1 2) (gammaGen 1 3) * bv 0
    - wedgeMat (gammaGen 1 0) (gammaGen 1 3) * bv 2
    + wedgeMat (gammaGen 1 0) (gammaGen 1 3) * bv 3
    + wedgeMat (gammaGen 1 1) (gammaGen 1 2) * bv 2
    - wedgeMat (gammaGen 1 1) (gammaGen 1 2) * bv 3
    - wedgeMat (gammaGen 1 0) (gammaGen 1 1) * bv 5
    + wedgeMat (gammaGen 1 2) (gammaGen 1 3) * bv 5 := by
  rw [w1]
  norm_num

lemma w2_eq : w2 1 = wedgeMat (gammaGen 1 0) (gammaGen 1 3) * bv 0
    - wedgeMat (gammaGen 1 0) (gammaGen 1 3) * bv 5
    - wedgeMat (gammaGen 1 0) (gammaGen 1 1) * bv 3
    + wedgeMat (gammaGen 1 2) (gammaGen 1 3) * bv 3
    + wedgeMat (gammaGen 1 0) (gammaGen 1 1) * bv 2
    - wedgeMat (gammaGen 1 2) (gammaGen 1 3) * bv 2
    - wedgeMat (gammaGen 1 1) (gammaGen 1 2) * bv 0
    + wedgeMat (gammaGen 1 1) (gammaGen 1 2) * bv 5 := by
  rw [w2]
  norm_num


theorem proof :
    ∀ n : Fin 6 → Fin 6 → ℤ,
      (∀ k l : Fin 6,
          ∑ j : Fin 6, (n k j : T) * wcoef 1 j l = ∑ j : Fin 6, (n l j : T) * wcoef 1 j k) →
      (∑ j : Fin 6, (n 0 j : T) * wcoef 1 j 5 - ∑ j : Fin 6, (n 1 j : T) * wcoef 1 j 4
          + ∑ j : Fin 6, (n 2 j : T) * wcoef 1 j 3 = 0) →
      (∑ k : Fin 6, (∑ j : Fin 6, (n k j : T) * gm 1 j) * bv k) ∈ weilLattice 1 := by
  intro n hsym hpl
  have hz : ∀ (p : Fin 4 → ℤ) (k l : Fin 6),
      ∑ j : Fin 6, n k j * wcz p j l = ∑ j : Fin 6, n l j * wcz p j k := by
    intro p k l
    have h := congrArg (ep p) (hsym k l)
    simp only [map_sum, map_mul, map_intCast, ep_wcoef] at h
    exact_mod_cast h
  have hpz : ∀ p : Fin 4 → ℤ,
      ∑ j : Fin 6, n 0 j * wcz p j 5 - ∑ j : Fin 6, n 1 j * wcz p j 4
        + ∑ j : Fin 6, n 2 j * wcz p j 3 = 0 := by
    intro p
    have h := congrArg (ep p) hpl
    simp only [map_add, map_sub, map_sum, map_mul, map_intCast, ep_wcoef, map_zero] at h
    exact_mod_cast h

  have s0_0_1 := hz P0 0 1
  simp [Fin.sum_univ_six] at s0_0_1
  have s0_1_2 := hz P0 1 2
  simp [Fin.sum_univ_six] at s0_1_2
  have s0_1_3 := hz P0 1 3
  simp [Fin.sum_univ_six] at s0_1_3
  have s0_1_4 := hz P0 1 4
  simp [Fin.sum_univ_six] at s0_1_4
  have s0_1_5 := hz P0 1 5
  simp [Fin.sum_univ_six] at s0_1_5
  have s1_0_1 := hz P1 0 1
  simp [Fin.sum_univ_six] at s1_0_1
  have s1_0_2 := hz P1 0 2
  simp [Fin.sum_univ_six] at s1_0_2
  have s1_0_3 := hz P1 0 3
  simp [Fin.sum_univ_six] at s1_0_3
  have s1_0_4 := hz P1 0 4
  simp [Fin.sum_univ_six] at s1_0_4
  have s1_0_5 := hz P1 0 5
  simp [Fin.sum_univ_six] at s1_0_5
  have s1_1_2 := hz P1 1 2
  simp [Fin.sum_univ_six] at s1_1_2
  have s1_1_3 := hz P1 1 3
  simp [Fin.sum_univ_six] at s1_1_3
  have s1_1_4 := hz P1 1 4
  simp [Fin.sum_univ_six] at s1_1_4
  have s1_1_5 := hz P1 1 5
  simp [Fin.sum_univ_six] at s1_1_5
  have s1_2_3 := hz P1 2 3
  simp [Fin.sum_univ_six] at s1_2_3
  have s1_2_4 := hz P1 2 4
  simp [Fin.sum_univ_six] at s1_2_4
  have s1_2_5 := hz P1 2 5
  simp [Fin.sum_univ_six] at s1_2_5
  have s1_3_4 := hz P1 3 4
  simp [Fin.sum_univ_six] at s1_3_4
  have s1_3_5 := hz P1 3 5
  simp [Fin.sum_univ_six] at s1_3_5
  have s1_4_5 := hz P1 4 5
  simp [Fin.sum_univ_six] at s1_4_5
  have s2_0_4 := hz P2 0 4
  simp [Fin.sum_univ_six] at s2_0_4
  have s2_1_4 := hz P2 1 4
  simp [Fin.sum_univ_six] at s2_1_4
  have s2_2_4 := hz P2 2 4
  simp [Fin.sum_univ_six] at s2_2_4
  have s2_3_4 := hz P2 3 4
  simp [Fin.sum_univ_six] at s2_3_4
  have s2_4_5 := hz P2 4 5
  simp [Fin.sum_univ_six] at s2_4_5
  have s3_0_1 := hz P3 0 1
  simp [Fin.sum_univ_six] at s3_0_1
  have s3_0_2 := hz P3 0 2
  simp [Fin.sum_univ_six] at s3_0_2
  have s3_0_3 := hz P3 0 3
  simp [Fin.sum_univ_six] at s3_0_3
  have s3_0_4 := hz P3 0 4
  simp [Fin.sum_univ_six] at s3_0_4
  have s3_0_5 := hz P3 0 5
  simp [Fin.sum_univ_six] at s3_0_5
  have s3_1_2 := hz P3 1 2
  simp [Fin.sum_univ_six] at s3_1_2
  have s3_1_3 := hz P3 1 3
  simp [Fin.sum_univ_six] at s3_1_3
  have s3_1_4 := hz P3 1 4
  simp [Fin.sum_univ_six] at s3_1_4
  have s3_1_5 := hz P3 1 5
  simp [Fin.sum_univ_six] at s3_1_5
  have s3_2_3 := hz P3 2 3
  simp [Fin.sum_univ_six] at s3_2_3
  have s3_2_4 := hz P3 2 4
  simp [Fin.sum_univ_six] at s3_2_4
  have s3_2_5 := hz P3 2 5
  simp [Fin.sum_univ_six] at s3_2_5
  have s3_3_4 := hz P3 3 4
  simp [Fin.sum_univ_six] at s3_3_4
  have s3_3_5 := hz P3 3 5
  simp [Fin.sum_univ_six] at s3_3_5
  have s3_4_5 := hz P3 4 5
  simp [Fin.sum_univ_six] at s3_4_5
  have q0 := hpz P0
  simp [Fin.sum_univ_six] at q0
  have q1 := hpz P1
  simp [Fin.sum_univ_six] at q1
  have q2 := hpz P2
  simp [Fin.sum_univ_six] at q2
  have q3 := hpz P3
  simp [Fin.sum_univ_six] at q3

  set m0 : ℤ := n 1 1 with hm0
  set m1 : ℤ := n 0 0 - n 1 1 with hm1
  set m2 : ℤ := n 0 2 with hm2
  have key : n 0 0 = m0 + m1 ∧ n 0 1 = 0 ∧ n 0 2 = m2 ∧ n 0 3 = -m2 ∧ n 0 4 = 0 ∧
      n 0 5 = -m1 ∧
      n 1 0 = 0 ∧ n 1 1 = m0 ∧ n 1 2 = 0 ∧ n 1 3 = 0 ∧ n 1 4 = 0 ∧ n 1 5 = 0 ∧
      n 2 0 = m2 ∧ n 2 1 = 0 ∧ n 2 2 = m0 - m1 ∧ n 2 3 = m1 ∧ n 2 4 = 0 ∧ n 2 5 = -m2 ∧
      n 3 0 = -m2 ∧ n 3 1 = 0 ∧ n 3 2 = m1 ∧ n 3 3 = m0 - m1 ∧ n 3 4 = 0 ∧ n 3 5 = m2 ∧
      n 4 0 = 0 ∧ n 4 1 = 0 ∧ n 4 2 = 0 ∧ n 4 3 = 0 ∧ n 4 4 = m0 ∧ n 4 5 = 0 ∧
      n 5 0 = -m1 ∧ n 5 1 = 0 ∧ n 5 2 = -m2 ∧ n 5 3 = m2 ∧ n 5 4 = 0 ∧ n 5 5 = m0 + m1 := by
    omega
  obtain ⟨k00, k01, k02, k03, k04, k05, k10, k11, k12, k13, k14, k15,
          k20, k21, k22, k23, k24, k25, k30, k31, k32, k33, k34, k35,
          k40, k41, k42, k43, k44, k45, k50, k51, k52, k53, k54, k55⟩ := key
  have hclass : (∑ k : Fin 6, (∑ j : Fin 6, (n k j : T) * gm 1 j) * bv k)
      = (m0 : T) * theta 1 + (m1 : T) * w1 1 + (m2 : T) * w2 1 := by
    simp only [Fin.sum_univ_six, k00, k01, k02, k03, k04, k05, k10, k11, k12, k13, k14, k15,
      k20, k21, k22, k23, k24, k25, k30, k31, k32, k33, k34, k35,
      k40, k41, k42, k43, k44, k45, k50, k51, k52, k53, k54, k55,
      theta_eq, w1_eq, w2_eq, gmv0, gmv1, gmv2, gmv3, gmv4, gmv5]
    push_cast
    ring
  rw [hclass]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · rw [← zsmul_eq_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [← zsmul_eq_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [← zsmul_eq_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end

end Submissions.GammaOneSymPluckerLattice.Lat
