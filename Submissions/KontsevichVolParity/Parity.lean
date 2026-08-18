import Mathlib

/-!
# A parity obstruction on integral tautological classes

`Δ f := ψ₁₁ f - ψ₁₀ f - ψ₀₁ f + ψ₀₀ f`, where `ψ_{ε,η}` evaluates `a ↦ ε`, `c ↦ η`,
`x₁₂ ↦ 1` and every other variable to `0`, reads off the coefficient of `a c x₁₂²`.
It is even on every cell class and equals `1` on `θ` and on `w₁`.
-/

namespace Submissions.KontsevichVolParity.Parity

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
def wedge (u v : G2) (k : Fin 6) : ℤ :=
  u (bivFst k) * v (bivSnd k) - u (bivSnd k) * v (bivFst k)
noncomputable def wedgePoly (u v : G2) : T := ∑ k : Fin 6, ((wedge u v k : ℤ) : ℚ) • bv k
noncomputable def parPoly (s : Gp) : T := ∑ k : Fin 4, ((s k : ℤ) : ℚ) • pv k
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
abbrev TriInst : Type := G2P × Gp × G2 × G2
abbrev ParInst : Type := G2P × Gp × Gp × G2 × G2
noncomputable def triRHS (e : TriInst) : T :=
  parPoly e.2.1 ^ 2 * wedgePoly e.2.2.1 e.2.2.2 ^ 2
noncomputable def parRHS (e : ParInst) : T :=
  (2 : ℚ) • (parPoly e.2.1 * parPoly e.2.2.1 * wedgePoly e.2.2.2.1 e.2.2.2.2 ^ 2)
abbrev Cell : Type := TriInst ⊕ ParInst
noncomputable def cellVol : Cell → T
  | Sum.inl e => triRHS e
  | Sum.inr e => parRHS e

/-! ### The functional -/

noncomputable def pt (ε η : ℚ) : Fin 10 → ℚ := ![ε, 0, η, 0, 1, 0, 0, 0, 0, 0]

noncomputable def ψ (ε η : ℚ) : T →ₐ[ℚ] ℚ := MvPolynomial.aeval (pt ε η)

noncomputable def Δ (f : T) : ℚ := ψ 1 1 f - ψ 1 0 f - ψ 0 1 f + ψ 0 0 f

@[simp] lemma psi_pv0 (ε η : ℚ) : ψ ε η (pv 0) = ε := by simp [ψ, pv, pt]
@[simp] lemma psi_pv1 (ε η : ℚ) : ψ ε η (pv 1) = 0 := by simp [ψ, pv, pt]
@[simp] lemma psi_pv2 (ε η : ℚ) : ψ ε η (pv 2) = η := by simp [ψ, pv, pt]
@[simp] lemma psi_pv3 (ε η : ℚ) : ψ ε η (pv 3) = 0 := by simp [ψ, pv, pt]
@[simp] lemma psi_bv0 (ε η : ℚ) : ψ ε η (bv 0) = 1 := by simp [ψ, bv, pt]
@[simp] lemma psi_bv1 (ε η : ℚ) : ψ ε η (bv 1) = 0 := by simp [ψ, bv, pt]
@[simp] lemma psi_bv2 (ε η : ℚ) : ψ ε η (bv 2) = 0 := by simp [ψ, bv, pt]
@[simp] lemma psi_bv3 (ε η : ℚ) : ψ ε η (bv 3) = 0 := by simp [ψ, bv, pt]
@[simp] lemma psi_bv4 (ε η : ℚ) : ψ ε η (bv 4) = 0 := by simp [ψ, bv, pt]
@[simp] lemma psi_bv5 (ε η : ℚ) : ψ ε η (bv 5) = 0 := by simp [ψ, bv, pt]

/-- The `ε,η`-value of the `i`-th row of `A`. -/
def rr (A : G2P) (i : Fin 4) (ε η : ℚ) : ℚ := (A i 0 : ℚ) * ε + (A i 2 : ℚ) * η

lemma psi_parPoly (ε η : ℚ) (s : Gp) :
    ψ ε η (parPoly s) = (s 0 : ℚ) * ε + (s 2 : ℚ) * η := by
  rw [parPoly, map_sum, Fin.sum_univ_four]
  simp only [map_smul, smul_eq_mul, psi_pv0, psi_pv1, psi_pv2, psi_pv3]
  ring

lemma psi_rowPoly (ε η : ℚ) (A : G2P) (i : Fin 4) :
    ψ ε η (rowPoly A i) = rr A i ε η := by
  rw [rowPoly, map_sum, Fin.sum_univ_four]
  simp only [map_smul, smul_eq_mul, psi_pv0, psi_pv1, psi_pv2, psi_pv3, rr]
  ring

lemma psi_wedgePoly (ε η : ℚ) (u v : G2) :
    ψ ε η (wedgePoly u v) = (wedge u v 0 : ℚ) := by
  rw [wedgePoly, map_sum, Fin.sum_univ_six]
  simp only [map_smul, smul_eq_mul, psi_bv0, psi_bv1, psi_bv2, psi_bv3, psi_bv4, psi_bv5]
  ring

lemma psi_wedgeMat (ε η : ℚ) (A B : G2P) :
    ψ ε η (wedgeMat A B) = rr A 0 ε η * rr B 1 ε η - rr A 1 ε η * rr B 0 ε η := by
  rw [wedgeMat, map_sum, Fin.sum_univ_six]
  simp only [map_mul, map_sub, psi_rowPoly, psi_bv0, psi_bv1, psi_bv2, psi_bv3, psi_bv4, psi_bv5,
    bivFst, bivSnd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

lemma psi_theta (ε η : ℚ) (d : ℤ) : ψ ε η (theta d) = ε * η := by
  rw [theta, map_sum, Fin.sum_univ_six]
  simp only [map_mul, psi_wedgeMat, psi_bv0, psi_bv1, psi_bv2, psi_bv3, psi_bv4, psi_bv5,
    bivFst, bivSnd, gammaGen, rr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num

lemma psi_w1 (ε η : ℚ) (d : ℤ) : ψ ε η (w1 d) = ε * η := by
  simp only [w1, map_add, map_sub, map_smul, map_mul, smul_eq_mul, psi_wedgeMat,
    psi_bv0, psi_bv1, psi_bv2, psi_bv3, psi_bv4, psi_bv5, gammaGen, rr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num

lemma psi_w2 (ε η : ℚ) (d : ℤ) : ψ ε η (w2 d) = 0 := by
  simp only [w2, map_add, map_sub, map_smul, map_mul, smul_eq_mul, psi_wedgeMat,
    psi_bv0, psi_bv1, psi_bv2, psi_bv3, psi_bv4, psi_bv5, gammaGen, rr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num

lemma Delta_theta (d : ℤ) : Δ (theta d) = 1 := by
  simp [Δ, psi_theta]

lemma Delta_w1 (d : ℤ) : Δ (w1 d) = 1 := by
  simp [Δ, psi_w1]

lemma Delta_w2 (d : ℤ) : Δ (w2 d) = 0 := by
  simp [Δ, psi_w2]

lemma Delta_add (f g : T) : Δ (f + g) = Δ f + Δ g := by
  simp only [Δ, map_add]; ring

lemma Delta_zero : Δ 0 = 0 := by simp [Δ]

lemma Delta_sum {ι : Type} (s : Finset ι) (g : ι → T) :
    Δ (∑ i ∈ s, g i) = ∑ i ∈ s, Δ (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Delta_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Delta_add, ih]

lemma Delta_intMul (n : ℤ) (f : T) : Δ ((n : T) * f) = (n : ℚ) * Δ f := by
  simp only [Δ, map_mul, map_intCast]; ring

/-- `Δ` is even on every cell class. -/
lemma Delta_cellVol (z : Cell) : ∃ k : ℤ, Δ (cellVol z) = 2 * (k : ℚ) := by
  cases z with
  | inl e =>
      refine ⟨e.2.1 0 * e.2.1 2 * (wedge e.2.2.1 e.2.2.2 0) ^ 2, ?_⟩
      simp only [cellVol, triRHS, Δ, map_mul, map_pow, psi_parPoly, psi_wedgePoly]
      push_cast
      ring
  | inr e =>
      refine ⟨(e.2.1 0 * e.2.2.1 2 + e.2.1 2 * e.2.2.1 0)
                * (wedge e.2.2.2.1 e.2.2.2.2 0) ^ 2, ?_⟩
      simp only [cellVol, parRHS, Δ, map_smul, map_mul, map_pow, psi_parPoly, psi_wedgePoly,
        smul_eq_mul]
      push_cast
      ring

theorem proof :
    ∀ (d : ℤ) (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell) (n₁ n₂ n₃ : ℤ),
      ∑ i ∈ s, (c i : T) * cellVol (z i)
          = (n₁ : T) * theta d + (n₂ : T) * w1 d + (n₃ : T) * w2 d →
        Even (n₁ + n₂) := by
  intro d ι s c z n₁ n₂ n₃ h
  classical
  have hL : Δ (∑ i ∈ s, (c i : T) * cellVol (z i))
      = ∑ i ∈ s, (c i : ℚ) * Δ (cellVol (z i)) := by
    rw [Delta_sum]
    exact Finset.sum_congr rfl fun i _ => Delta_intMul _ _
  have hR : Δ ((n₁ : T) * theta d + (n₂ : T) * w1 d + (n₃ : T) * w2 d)
      = (n₁ : ℚ) + (n₂ : ℚ) := by
    rw [Delta_add, Delta_add, Delta_intMul, Delta_intMul, Delta_intMul,
      Delta_theta, Delta_w1, Delta_w2]
    ring
  choose kk hkk using Delta_cellVol
  have hEq : ((n₁ + n₂ : ℤ) : ℚ) = 2 * ((∑ i ∈ s, c i * kk (z i) : ℤ) : ℚ) := by
    push_cast
    rw [← hR, ← h, hL]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hkk]; ring
  have : n₁ + n₂ = 2 * (∑ i ∈ s, c i * kk (z i)) := by exact_mod_cast hEq
  exact ⟨_, by rw [this]; ring⟩

end

end Submissions.KontsevichVolParity.Parity
