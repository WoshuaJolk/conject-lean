import Mathlib

/-! # Zharkov's right-hand sides are (area 2-vector) ⊗ (framing), plus shoelace -/

namespace Submissions.CellVolIsArea.Area

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

def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

abbrev TriInst : Type := G2P × Gp × G2 × G2
abbrev ParInst : Type := G2P × Gp × Gp × G2 × G2

noncomputable def triRHS (e : TriInst) : T :=
  parPoly e.2.1 ^ 2 * wedgePoly e.2.2.1 e.2.2.2 ^ 2

noncomputable def parRHS (e : ParInst) : T :=
  (2 : ℚ) • (parPoly e.2.1 * parPoly e.2.2.1 * wedgePoly e.2.2.2.1 e.2.2.2.2 ^ 2)


/-! ### Bilinearity of `wedgeMat` -/

lemma rowPoly_add (A B : G2P) (i : Fin 4) :
    rowPoly (A + B) i = rowPoly A i + rowPoly B i := by
  simp only [rowPoly, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (A + B) i m = A i m + B i m := rfl
  rw [this]
  push_cast
  module

lemma rowPoly_sub (A B : G2P) (i : Fin 4) :
    rowPoly (A - B) i = rowPoly A i - rowPoly B i := by
  simp only [rowPoly, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (A - B) i m = A i m - B i m := rfl
  rw [this]
  push_cast
  module

lemma cast_smul (n : ℤ) (p : T) : ((n : ℤ) : ℚ) • p = ((n : ℤ) : T) * p := by
  rw [Int.cast_smul_eq_zsmul, zsmul_eq_mul]

lemma parPoly_eq (s : Gp) : parPoly s = ∑ m : Fin 4, ((s m : ℤ) : T) * pv m := by
  simp only [parPoly, cast_smul]

lemma rowPoly_eq (A : G2P) (i : Fin 4) : rowPoly A i = ∑ m : Fin 4, ((A i m : ℤ) : T) * pv m := by
  simp only [rowPoly, cast_smul]

lemma wedgePoly_eq (u v : G2) :
    wedgePoly u v = ∑ k : Fin 6, ((wedge u v k : ℤ) : T) * bv k := by
  simp only [wedgePoly, cast_smul]

lemma rowPoly_outer (u : G2) (s : Gp) (i : Fin 4) :
    rowPoly (outer u s) i = ((u i : ℤ) : T) * parPoly s := by
  rw [rowPoly_eq, parPoly_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : outer u s i m = u i * s m := rfl
  rw [this]
  push_cast
  ring

/-! ### The four identities -/

lemma tri_area (x : G2P) (s : Gp) (u v : G2) :
    triRHS (x, s, u, v) = wedgeMat (outer u s) (outer v s) * wedgePoly u v := by
  have h : wedgeMat (outer u s) (outer v s) = parPoly s ^ 2 * wedgePoly u v := by
    rw [wedgeMat, wedgePoly_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rowPoly_outer, rowPoly_outer, rowPoly_outer, rowPoly_outer]
    have : wedge u v k
        = u (bivFst k) * v (bivSnd k) - u (bivSnd k) * v (bivFst k) := rfl
    rw [this]
    push_cast
    ring
  rw [h, triRHS]
  ring

lemma par_area (x : G2P) (s t : Gp) (u v : G2) :
    parRHS (x, s, t, u, v) = wedgeMat (outer u s) (outer v t) * wedgePoly u v
      + wedgeMat (outer u s) (outer v t) * wedgePoly u v := by
  have h : wedgeMat (outer u s) (outer v t) = parPoly s * parPoly t * wedgePoly u v := by
    rw [wedgeMat, wedgePoly_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rowPoly_outer, rowPoly_outer, rowPoly_outer, rowPoly_outer]
    have : wedge u v k
        = u (bivFst k) * v (bivSnd k) - u (bivSnd k) * v (bivFst k) := rfl
    rw [this]
    push_cast
    ring
  rw [h, parRHS, two_smul]
  push_cast
  ring

lemma shoelace_tri (x p q : G2P) :
    wedgeMat x q + wedgeMat (x + q) (p - q) + wedgeMat p q = wedgeMat x p := by
  simp only [wedgeMat, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [rowPoly_add, rowPoly_sub]
  ring

lemma shoelace_par (x p q : G2P) :
    wedgeMat (x + q) p + wedgeMat x q + wedgeMat p q + wedgeMat p q
      = wedgeMat x p + wedgeMat (x + p) q := by
  simp only [wedgeMat, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [rowPoly_add]
  ring

theorem proof :
    (∀ (x : G2P) (s : Gp) (u v : G2),
        triRHS (x, s, u, v) = wedgeMat (outer u s) (outer v s) * wedgePoly u v) ∧
    (∀ (x : G2P) (s t : Gp) (u v : G2),
        parRHS (x, s, t, u, v) = wedgeMat (outer u s) (outer v t) * wedgePoly u v
          + wedgeMat (outer u s) (outer v t) * wedgePoly u v) ∧
    (∀ x p q : G2P,
        wedgeMat x q + wedgeMat (x + q) (p - q) + wedgeMat p q = wedgeMat x p) ∧
    (∀ x p q : G2P,
        wedgeMat (x + q) p + wedgeMat x q + wedgeMat p q + wedgeMat p q
          = wedgeMat x p + wedgeMat (x + p) q) :=
  ⟨tri_area, par_area, shoelace_tri, shoelace_par⟩

end

end Submissions.CellVolIsArea.Area
