import Mathlib

/-! # The Plücker relation on tautological chain classes -/

namespace Submissions.ChainClassPlucker.Plk

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

noncomputable def evp (p : Fin 4 → ℚ) (m0 m1 m2 m3 m4 m5 : ℚ) : T →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval ![p 0, p 1, p 2, p 3, m0, m1, m2, m3, m4, m5]

noncomputable def plucker (p : Fin 4 → ℚ) (f : T) : ℚ :=
  (evp p 1 0 0 0 0 1 f - evp p 1 0 0 0 0 0 f - evp p 0 0 0 0 0 1 f + evp p 0 0 0 0 0 0 f)
    - (evp p 0 1 0 0 1 0 f - evp p 0 1 0 0 0 0 f - evp p 0 0 0 0 1 0 f + evp p 0 0 0 0 0 0 f)
    + (evp p 0 0 1 1 0 0 f - evp p 0 0 1 0 0 0 f - evp p 0 0 0 1 0 0 f + evp p 0 0 0 0 0 0 f)

/-! ### Evaluation lemmas -/

variable (p : Fin 4 → ℚ) (m0 m1 m2 m3 m4 m5 : ℚ)

@[simp] lemma evp_pv (l : Fin 4) : evp p m0 m1 m2 m3 m4 m5 (pv l) = p l := by
  fin_cases l <;> simp [evp, pv]

lemma evp_bv0 : evp p m0 m1 m2 m3 m4 m5 (bv 0) = m0 := by simp [evp, bv]
lemma evp_bv1 : evp p m0 m1 m2 m3 m4 m5 (bv 1) = m1 := by simp [evp, bv]
lemma evp_bv2 : evp p m0 m1 m2 m3 m4 m5 (bv 2) = m2 := by simp [evp, bv]
lemma evp_bv3 : evp p m0 m1 m2 m3 m4 m5 (bv 3) = m3 := by simp [evp, bv]
lemma evp_bv4 : evp p m0 m1 m2 m3 m4 m5 (bv 4) = m4 := by simp [evp, bv]
lemma evp_bv5 : evp p m0 m1 m2 m3 m4 m5 (bv 5) = m5 := by simp [evp, bv]

lemma evp_parPoly (s : Gp) :
    evp p m0 m1 m2 m3 m4 m5 (parPoly s)
      = (s 0 : ℚ) * p 0 + (s 1 : ℚ) * p 1 + (s 2 : ℚ) * p 2 + (s 3 : ℚ) * p 3 := by
  rw [parPoly, map_sum, Fin.sum_univ_four]
  simp only [map_smul, smul_eq_mul, evp_pv]

lemma evp_wedgePoly (u v : G2) :
    evp p m0 m1 m2 m3 m4 m5 (wedgePoly u v)
      = (wedge u v 0 : ℚ) * m0 + (wedge u v 1 : ℚ) * m1 + (wedge u v 2 : ℚ) * m2
        + (wedge u v 3 : ℚ) * m3 + (wedge u v 4 : ℚ) * m4 + (wedge u v 5 : ℚ) * m5 := by
  rw [wedgePoly, map_sum, Fin.sum_univ_six]
  simp only [map_smul, smul_eq_mul, evp_bv0, evp_bv1, evp_bv2, evp_bv3, evp_bv4, evp_bv5]

/-- The Pfaffian of a decomposable bivector vanishes. -/
lemma pfaff (u v : G2) :
    ((wedge u v 0 : ℤ) : ℚ) * (wedge u v 5 : ℤ) - ((wedge u v 1 : ℤ) : ℚ) * (wedge u v 4 : ℤ)
      + ((wedge u v 2 : ℤ) : ℚ) * (wedge u v 3 : ℤ) = 0 := by
  have e0 : wedge u v 0 = u 0 * v 1 - u 1 * v 0 := rfl
  have e1 : wedge u v 1 = u 0 * v 2 - u 2 * v 0 := rfl
  have e2 : wedge u v 2 = u 0 * v 3 - u 3 * v 0 := rfl
  have e3 : wedge u v 3 = u 1 * v 2 - u 2 * v 1 := rfl
  have e4 : wedge u v 4 = u 1 * v 3 - u 3 * v 1 := rfl
  have e5 : wedge u v 5 = u 2 * v 3 - u 3 * v 2 := rfl
  rw [e0, e1, e2, e3, e4, e5]; push_cast; ring

/-- On `q · (u ∧ v)²` with `q` free of the `x`'s, `plucker` returns `2 q(p) Pf(u ∧ v) = 0`. -/
lemma plucker_sq (q : T)
    (hq : ∀ n0 n1 n2 n3 n4 n5 : ℚ, evp p n0 n1 n2 n3 n4 n5 q = evp p 0 0 0 0 0 0 q)
    (u v : G2) : plucker p (q * wedgePoly u v ^ 2) = 0 := by
  have key : ∀ n0 n1 n2 n3 n4 n5 : ℚ, evp p n0 n1 n2 n3 n4 n5 (q * wedgePoly u v ^ 2)
      = evp p 0 0 0 0 0 0 q
        * ((wedge u v 0 : ℚ) * n0 + (wedge u v 1 : ℚ) * n1 + (wedge u v 2 : ℚ) * n2
            + (wedge u v 3 : ℚ) * n3 + (wedge u v 4 : ℚ) * n4 + (wedge u v 5 : ℚ) * n5) ^ 2 := by
    intro n0 n1 n2 n3 n4 n5
    rw [map_mul, map_pow, evp_wedgePoly, hq]
  have hpf := pfaff u v
  simp only [plucker, key]
  linear_combination (2 * evp p 0 0 0 0 0 0 q) * hpf

lemma plucker_cellVol (z : Cell) : plucker p (cellVol z) = 0 := by
  cases z with
  | inl e =>
      show plucker p (parPoly e.2.1 ^ 2 * wedgePoly e.2.2.1 e.2.2.2 ^ 2) = 0
      refine plucker_sq p _ (fun n0 n1 n2 n3 n4 n5 => ?_) _ _
      rw [map_pow, map_pow, evp_parPoly, evp_parPoly]
  | inr e =>
      have hr : cellVol (Sum.inr e)
          = ((2 : ℚ) • (parPoly e.2.1 * parPoly e.2.2.1))
              * wedgePoly e.2.2.2.1 e.2.2.2.2 ^ 2 := by
        show parRHS e = _
        rw [parRHS, smul_mul_assoc]
      rw [hr]
      refine plucker_sq p _ (fun n0 n1 n2 n3 n4 n5 => ?_) _ _
      rw [map_smul, map_smul, map_mul, map_mul, evp_parPoly, evp_parPoly, evp_parPoly,
        evp_parPoly]

lemma plucker_sum {ι : Type} (s : Finset ι) (g : ι → T) :
    plucker p (∑ i ∈ s, g i) = ∑ i ∈ s, plucker p (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [plucker]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [plucker, map_add]
      ring

lemma plucker_intMul (n : ℤ) (f : T) :
    plucker p ((n : T) * f) = (n : ℚ) * plucker p f := by
  simp only [plucker, map_mul, map_intCast]
  ring

theorem proof :
    ∀ (p : Fin 4 → ℚ) (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
      plucker p (∑ i ∈ s, (c i : T) * cellVol (z i)) = 0 := by
  intro p ι s c z
  rw [plucker_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [plucker_intMul, plucker_cellVol, mul_zero]

end

end Submissions.ChainClassPlucker.Plk
