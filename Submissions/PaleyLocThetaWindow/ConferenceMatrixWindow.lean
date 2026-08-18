import Commons.PaleyLocalizationTheta
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace Submissions.PaleyLocThetaWindow.ConferenceMatrixWindow


variable {p : ℕ} [Fact (Nat.Prime p)]

/-- the quadratic character of `ZMod p`, as a real number -/
noncomputable def chi (p : ℕ) [Fact (Nat.Prime p)] (z : ZMod p) : ℝ :=
  ((quadraticChar (ZMod p) z : ℤ) : ℝ)

lemma chi_zero : chi p 0 = 0 := by simp [chi]

lemma chi_mul (a b : ZMod p) : chi p (a * b) = chi p a * chi p b := by
  simp [chi, map_mul]

lemma chi_sum_zero (hp2 : p ≠ 2) : ∑ a : ZMod p, chi p a = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2
  have := quadraticChar_sum_zero (F := ZMod p) hF
  simp only [chi]
  rw [← Int.cast_sum, ← Int.cast_zero]
  norm_cast

lemma chi_sq (a : ZMod p) (ha : a ≠ 0) : chi p a * chi p a = 1 := by
  have := quadraticChar_sq_one (F := ZMod p) ha
  simp only [chi, ← Int.cast_mul]
  rw [show (quadraticChar (ZMod p) a : ℤ) * (quadraticChar (ZMod p) a) = (quadraticChar (ZMod p) a)^2 by ring, this]
  norm_num


variable {p : ℕ} [Fact (Nat.Prime p)]

lemma chi_neg_one (hp4 : p % 4 = 1) : chi p (-1) = 1 := by
  have hne : (-1 : ZMod p) ≠ 0 := by
    have : (1 : ZMod p) ≠ 0 := one_ne_zero
    simpa using this
  have hsq : IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have := (quadraticChar_one_iff_isSquare (F := ZMod p) hne).mpr hsq
  simp [chi, this]

/-- the basic Jacobi sum `∑ s, χ(s)χ(s-1) = -1`. -/
lemma jac (hp4 : p % 4 = 1) : ∑ s : ZMod p, chi p s * chi p (s - 1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2
  have hq := quadraticChar_isQuadratic (F := ZMod p)
  have hne1 : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one hF
  have hJ : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = - quadraticChar (ZMod p) (-1) := by
    have := jacobiSum_nontrivial_inv (F := ZMod p) (R := ℤ) hne1
    rwa [hq.inv] at this
  have hc : quadraticChar (ZMod p) (-1) = 1 := by
    have hne : (-1 : ZMod p) ≠ 0 := by simpa using (one_ne_zero : (1:ZMod p) ≠ 0)
    exact (quadraticChar_one_iff_isSquare (F := ZMod p) hne).mpr
      (by rw [ZMod.exists_sq_eq_neg_one_iff]; omega)
  have hstep : ∀ s : ZMod p, chi p s * chi p (s - 1) = chi p s * chi p (1 - s) := by
    intro s
    have : (s - 1 : ZMod p) = (-1) * (1 - s) := by ring
    rw [this, chi_mul, chi_neg_one hp4, one_mul]
  simp only [hstep]
  have : ∑ s : ZMod p, chi p s * chi p (1 - s)
      = ((jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) : ℤ) : ℝ) := by
    simp [jacobiSum, chi, Int.cast_sum]
  rw [this, hJ, hc]
  norm_num


open Matrix

/-- The Frobenius pairing of two positive semidefinite real matrices is nonnegative. -/
theorem trace_mul_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {M X : Matrix V V ℝ} (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace := by
  classical
  have hH : M.IsHermitian := hM.isHermitian
  set U : Matrix V V ℝ := (Matrix.IsHermitian.eigenvectorUnitary hH : Matrix V V ℝ) with hU
  set D : Matrix V V ℝ := Matrix.diagonal (RCLike.ofReal ∘ Matrix.IsHermitian.eigenvalues hH)
    with hD
  have hMe : M = U * D * star U := by
    conv_lhs => rw [Matrix.IsHermitian.spectral_theorem hH]
    rw [Unitary.conjStarAlgAut_apply]
  have hY : ((star U) * X * U).PosSemidef := by
    have := Matrix.PosSemidef.conjTranspose_mul_mul_same hX U
    rwa [← Matrix.star_eq_conjTranspose] at this
  have htr : (M * X).trace = (D * ((star U) * X * U)).trace := by
    rw [hMe, Matrix.trace_mul_comm]
    have e1 : X * (U * D * star U) = (X * U * D) * star U := by
      simp [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    have e2 : star U * (X * U * D) = (star U * X * U) * D := by
      simp [Matrix.mul_assoc]
    rw [e2, Matrix.trace_mul_comm]
  rw [htr]
  have hdiag : (D * ((star U) * X * U)).trace
      = ∑ i, Matrix.IsHermitian.eigenvalues hH i * ((star U) * X * U) i i := by
    simp [Matrix.trace, Matrix.mul_apply, hD, Matrix.diagonal_apply, Finset.sum_ite_eq]
  rw [hdiag]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Matrix.PosSemidef.diag_nonneg hY)
  exact Matrix.PosSemidef.eigenvalues_nonneg hM i


variable {p : ℕ} [Fact (Nat.Prime p)]

lemma chi_isSq {z : ZMod p} (hz : Commons.IsNonzeroSq z) : chi p z = 1 := by
  have := (quadraticChar_one_iff_isSquare (F := ZMod p) hz.1).mpr
    (by obtain ⟨r, hr⟩ := hz.2; exact ⟨r, hr⟩)
  simp [chi, this]

lemma sum_ite_card (b : ZMod p) :
    ∑ a : ZMod p, (if a = b then (0:ℝ) else 1) = (p : ℝ) - 1 := by
  have : ∑ a : ZMod p, (if a = b then (0:ℝ) else 1)
      = (∑ _a : ZMod p, (1:ℝ)) - ∑ a : ZMod p, (if a = b then (1:ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by by_cases h : a = b <;> simp [h])
  rw [this]
  simp [Finset.sum_ite_eq', ZMod.card]

lemma key (hp4 : p % 4 = 1) (b c : ZMod p) :
    ∑ a : ZMod p, chi p (a - b) * chi p (a - c) = if b = c then ((p:ℝ) - 1) else -1 := by
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl]
    have h1 : ∀ a : ZMod p, chi p (a - b) * chi p (a - b) = if a = b then (0:ℝ) else 1 := by
      intro a
      by_cases h : a = b
      · simp [h, chi_zero]
      · rw [if_neg h]; exact chi_sq _ (sub_ne_zero.mpr h)
    rw [Finset.sum_congr rfl (fun a _ => h1 a), sum_ite_card]
  · rw [if_neg hbc]
    set d : ZMod p := c - b with hd
    have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
    have := jac (p := p) hp4
    rw [← this]
    refine (Fintype.sum_equiv ((Equiv.mulLeft₀ d hd0).trans (Equiv.addLeft b))
      (fun s => chi p s * chi p (s - 1)) (fun a => chi p (a - b) * chi p (a - c)) ?_).symm
    intro s
    have e1 : b + d * s - b = d * s := by ring
    have e2 : b + d * s - c = d * (s - 1) := by rw [hd]; ring
    show chi p s * chi p (s - 1) = chi p (b + d * s - b) * chi p (b + d * s - c)
    rw [e1, e2, chi_mul, chi_mul]
    have hdd : chi p d * chi p d = 1 := chi_sq _ hd0
    rw [show chi p d * chi p s * (chi p d * chi p (s - 1))
        = (chi p d * chi p d) * (chi p s * chi p (s - 1)) from by ring, hdd, one_mul]


open Matrix
variable {p : ℕ} [Fact (Nat.Prime p)]

/-- the Paley conference matrix -/
noncomputable def Hf (p : ℕ) [Fact (Nat.Prime p)] : Matrix (ZMod p) (ZMod p) ℝ :=
  Matrix.of fun a b => chi p (a - b)

lemma Hf_symm (hp4 : p % 4 = 1) : (Hf p)ᵀ = Hf p := by
  ext a b
  show chi p (b - a) = chi p (a - b)
  have : (b - a : ZMod p) = (-1) * (a - b) := by ring
  rw [this, chi_mul, chi_neg_one hp4, one_mul]

lemma Hf_sq (hp4 : p % 4 = 1) :
    Hf p * Hf p = (p : ℝ) • (1 : Matrix (ZMod p) (ZMod p) ℝ)
      - Matrix.of (fun _ _ : ZMod p => (1:ℝ)) := by
  ext a b
  have hflip : ∀ x y : ZMod p, chi p (x - y) = chi p (y - x) := by
    intro x y
    have : (x - y : ZMod p) = (-1) * (y - x) := by ring
    rw [this, chi_mul, chi_neg_one hp4, one_mul]
  have : (Hf p * Hf p) a b = ∑ c : ZMod p, chi p (c - a) * chi p (c - b) := by
    simp only [Hf, Matrix.mul_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hflip a c, hflip c b, hflip b c]
  rw [this, key hp4 a b]
  by_cases h : a = b
  · simp [h, Matrix.one_apply]
  · simp [h, Matrix.one_apply, Ne.symm h]


open Matrix
variable {p : ℕ} [Fact (Nat.Prime p)]

lemma dot_Hf_sq (hp4 : p % 4 = 1) (x : ZMod p → ℝ) :
    (Hf p *ᵥ x) ⬝ᵥ (Hf p *ᵥ x) = (p:ℝ) * (x ⬝ᵥ x) - (∑ a, x a)^2 := by
  have expand : ∀ a : ZMod p,
      (∑ b, chi p (a - b) * x b) * (∑ c, chi p (a - c) * x c)
        = ∑ b, ∑ c, (chi p (a - b) * chi p (a - c)) * (x b * x c) := by
    intro a
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have lhs : (Hf p *ᵥ x) ⬝ᵥ (Hf p *ᵥ x)
      = ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p,
          (chi p (a - b) * chi p (a - c)) * (x b * x c) := by
    simp only [dotProduct, Matrix.mulVec, Hf, Matrix.of_apply, dotProduct]
    exact Finset.sum_congr rfl fun a _ => expand a
  have swap : ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p,
        (chi p (a - b) * chi p (a - c)) * (x b * x c)
      = ∑ b : ZMod p, ∑ c : ZMod p,
          (∑ a : ZMod p, chi p (a - b) * chi p (a - c)) * (x b * x c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul]
  rw [lhs, swap]
  have ev : ∀ b c : ZMod p, (∑ a : ZMod p, chi p (a - b) * chi p (a - c)) * (x b * x c)
      = ((p:ℝ) * (if b = c then (1:ℝ) else 0) - 1) * (x b * x c) := by
    intro b c
    rw [key hp4 b c]
    by_cases h : b = c <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ev b c]
  have split : ∀ b : ZMod p, ∑ c : ZMod p, ((p:ℝ) * (if b = c then (1:ℝ) else 0) - 1) * (x b * x c)
      = (p:ℝ) * (x b * x b) - x b * (∑ c, x c) := by
    intro b
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [show (fun c => (p:ℝ) * (if b = c then (1:ℝ) else 0) * (x b * x c))
        = (fun c => if b = c then (p:ℝ) * (x b * x b) else 0) from by
          funext c; by_cases h : b = c <;> simp [h]]
      simp
    · rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun b _ => split b]
  rw [Finset.sum_sub_distrib]
  have : ∑ b : ZMod p, (p:ℝ) * (x b * x b) = (p:ℝ) * (x ⬝ᵥ x) := by
    rw [← Finset.mul_sum]; rfl
  rw [this]
  have h2 : ∑ b : ZMod p, x b * (∑ c, x c) = (∑ a, x a)^2 := by
    rw [← Finset.sum_mul]; ring
  rw [h2]

/-- `√p • 1 - e • H` is positive semidefinite for `e = ±1`. -/
lemma B_posSemidef (hp4 : p % 4 = 1) (e : ℝ) (he : e * e = 1) :
    ((Real.sqrt p : ℝ) • (1 : Matrix (ZMod p) (ZMod p) ℝ) - e • Hf p).PosSemidef := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have := (Fact.out : Nat.Prime p).pos
    exact_mod_cast this
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hss : Real.sqrt p * Real.sqrt p = (p:ℝ) := Real.mul_self_sqrt (le_of_lt hp0)
  have hflip : ∀ u v : ZMod p, chi p (u - v) = chi p (v - u) := by
    intro u v
    have h : (u - v : ZMod p) = (-1) * (v - u) := by ring
    rw [h, chi_mul, chi_neg_one hp4, one_mul]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Hf, Matrix.of_apply, smul_eq_mul]
    rw [hflip b a]
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro x
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hCS : (x ⬝ᵥ (Hf p *ᵥ x))^2 ≤ (x ⬝ᵥ x) * ((Hf p *ᵥ x) ⬝ᵥ (Hf p *ᵥ x)) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (Hf p *ᵥ x)
      simpa [dotProduct, sq] using h
    have hnorm := dot_Hf_sq (p := p) hp4 x
    have hbound : (x ⬝ᵥ (Hf p *ᵥ x))^2 ≤ (p:ℝ) * (x ⬝ᵥ x)^2 := by
      nlinarith [sq_nonneg (∑ a, x a), hxx]
    have hval : star x ⬝ᵥ (((Real.sqrt p : ℝ) • (1 : Matrix (ZMod p) (ZMod p) ℝ)
        - e • Hf p) *ᵥ x) = Real.sqrt p * (x ⬝ᵥ x) - e * (x ⬝ᵥ (Hf p *ᵥ x)) := by
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
        Matrix.one_mulVec, star_trivial]
    rw [hval]
    have hb0 : 0 ≤ Real.sqrt p * (x ⬝ᵥ x) := mul_nonneg (le_of_lt hs0) hxx
    have heq : (e * (x ⬝ᵥ (Hf p *ᵥ x)))^2 = (x ⬝ᵥ (Hf p *ᵥ x))^2 := by
      have : (e * (x ⬝ᵥ (Hf p *ᵥ x)))^2 = (e * e) * (x ⬝ᵥ (Hf p *ᵥ x))^2 := by ring
      rw [this, he, one_mul]
    have hle : e * (x ⬝ᵥ (Hf p *ᵥ x)) ≤ Real.sqrt p * (x ⬝ᵥ x) := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hbound, hss, hb0, heq]
    linarith


open Matrix Commons
variable {p : ℕ} [Fact (Nat.Prime p)]

theorem feasible_le (hp4 : p % 4 = 1) :
    ∀ s ∈ (haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
      Commons.thetaCliqueFeasible (Commons.paleyLocAdj p)), s ≤ 1 + Real.sqrt p := by
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have := (Fact.out : Nat.Prime p).pos; exact_mod_cast this
  haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
  have hsnn : (0:ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  rintro s ⟨X, hX, htr, hzero, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ,
      M = (((Real.sqrt p : ℝ) • (1 : Matrix (ZMod p) (ZMod p) ℝ)
        - (1:ℝ) • Hf p)).submatrix Subtype.val Subtype.val := ⟨_, rfl⟩
  have hMpsd : M.PosSemidef := by
    rw [hM]; exact Matrix.PosSemidef.submatrix (B_posSemidef hp4 1 (by norm_num)) Subtype.val
  have hkey : 0 ≤ (M * X).trace := trace_mul_nonneg hMpsd hX
  have hsym : ∀ u v : Commons.PaleyLocV p, X u v = X v u := by
    intro u v
    have h := congrFun (congrFun hX.isHermitian u) v
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hcoe : ∀ u v : Commons.PaleyLocV p, ((u : ZMod p) = (v : ZMod p)) ↔ u = v :=
    fun u v => ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
  have hMval : ∀ u v : Commons.PaleyLocV p,
      M u v = Real.sqrt p * (if u = v then (1:ℝ) else 0) - chi p ((u:ZMod p) - v) := by
    intro u v
    rw [hM]
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Hf, Matrix.of_apply, smul_eq_mul, one_smul]
    by_cases h : u = v <;> simp [h, hcoe u v]
  have hpt : ∀ u v : Commons.PaleyLocV p,
      M u v * X v u = (Real.sqrt p + 1) * (if u = v then X u u else 0) - X u v := by
    intro u v
    rw [hMval u v]
    by_cases h : u = v
    · subst h
      have hz0 : chi p ((u:ZMod p) - (u:ZMod p)) = 0 := by
        rw [sub_self]; exact chi_zero
      rw [hz0, if_pos rfl, if_pos rfl]
      ring
    · have hne : ((u : ZMod p) - v) ≠ 0 := fun hc => h ((hcoe u v).mp (by
        have := sub_eq_zero.mp hc; exact this))
      by_cases hadj : Commons.paleyLocAdj p u v
      · have hc1 : chi p ((u : ZMod p) - v) = 1 := chi_isSq hadj
        rw [hc1, ← hsym u v]
        simp only [if_neg h]
        ring
      · have hz : X u v = 0 := hzero u v h hadj
        rw [← hsym u v, hz]
        simp only [if_neg h]
        ring
  have hetr : (M * X).trace = ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, M u v * X v u := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  have hrow : ∀ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, M u v * X v u
      = (Real.sqrt p + 1) * X u u - ∑ v : Commons.PaleyLocV p, X u v := by
    intro u
    rw [Finset.sum_congr rfl fun v _ => hpt u v, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.mul_sum]
    simp
  have htrMX : (M * X).trace
      = (Real.sqrt p + 1) * (∑ u : Commons.PaleyLocV p, X u u)
        - ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v := by
    rw [hetr, Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have htr' : ∑ u : Commons.PaleyLocV p, X u u = 1 := by
    rw [← htr]; simp [Matrix.trace, Matrix.diag_apply]
  rw [htrMX, htr'] at hkey
  linarith

theorem upper (hp4 : p % 4 = 1) :
    Commons.paleyLocTheta p (Fact.out : Nat.Prime p).pos ≤ 1 + Real.sqrt p := by
  haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
  exact Real.sSup_le (feasible_le hp4) (by positivity)

theorem bdd (hp4 : p % 4 = 1) :
    haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
    BddAbove (Commons.thetaCliqueFeasible (Commons.paleyLocAdj p)) :=
  ⟨1 + Real.sqrt p, fun _ hx => feasible_le hp4 _ hx⟩


open Matrix Commons
variable {p : ℕ} [Fact (Nat.Prime p)]

lemma chi_notSq {z : ZMod p} (hz : z ≠ 0) (h : ¬ Commons.IsNonzeroSq z) : chi p z = -1 := by
  have hns : ¬ IsSquare z := fun hs => h ⟨hz, hs⟩
  have hq := (quadraticChar_neg_one_iff_not_isSquare (F := ZMod p) (a := z)).mpr hns
  simp [chi, hq]

lemma card_eq (hp4 : p % 4 = 1) :
    haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
    2 * (Fintype.card (Commons.PaleyLocV p) : ℝ) + 1 = (p:ℝ) := by
  haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
  have hp2 : p ≠ 2 := by omega
  have h0 : ∑ a : ZMod p, chi p a = 0 := chi_sum_zero hp2
  have hpt : ∀ a : ZMod p, chi p a + 1
      = (if Commons.IsNonzeroSq a then (2:ℝ) else 0) + (if a = 0 then (1:ℝ) else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      have hn : ¬ Commons.IsNonzeroSq (0 : ZMod p) := fun h => h.1 rfl
      rw [chi_zero, if_neg hn, if_pos rfl]
    · by_cases hs : Commons.IsNonzeroSq a
      · rw [chi_isSq hs, if_pos hs, if_neg ha]; ring
      · rw [chi_notSq ha hs, if_neg hs, if_neg ha]; ring
  have hsum : ∑ a : ZMod p, (chi p a + 1) = (p:ℝ) := by
    rw [Finset.sum_add_distrib, h0]
    simp [ZMod.card]
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib] at hsum
  have h1 : ∑ a : ZMod p, (if Commons.IsNonzeroSq a then (2:ℝ) else 0)
      = 2 * (Fintype.card (Commons.PaleyLocV p) : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [Fintype.card_subtype]
    ring
  have h2 : ∑ a : ZMod p, (if a = 0 then (1:ℝ) else 0) = 1 := by
    simp
  rw [h1, h2] at hsum
  exact hsum


open Matrix Commons
variable {p : ℕ} [Fact (Nat.Prime p)]

lemma allOnes_psd {V : Type*} [Fintype V] [DecidableEq V] :
    (Matrix.of (fun _ _ : V => (1:ℝ))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext a b; simp [Matrix.conjTranspose_apply]
  · intro x
    have : star x ⬝ᵥ ((Matrix.of (fun _ _ : V => (1:ℝ))) *ᵥ x) = (∑ a, x a) * (∑ a, x a) := by
      simp [dotProduct, Matrix.mulVec, Matrix.of_apply, ← Finset.sum_mul, star_trivial]
    rw [this]
    exact mul_self_nonneg _

/-- the compression of `√p • 1 - e • H` to the localization, entrywise -/
lemma sub_psd_entry (hp4 : p % 4 = 1) (e : ℝ) (he : e * e = 1) :
    haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
    ∃ P : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ, P.PosSemidef ∧
      ∀ u v, P u v = Real.sqrt p * (if u = v then (1:ℝ) else 0) - e * chi p ((u:ZMod p) - v) := by
  haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
  refine ⟨(((Real.sqrt p : ℝ) • (1 : Matrix (ZMod p) (ZMod p) ℝ) - e • Hf p)).submatrix
    Subtype.val Subtype.val, Matrix.PosSemidef.submatrix (B_posSemidef hp4 e he) Subtype.val, ?_⟩
  intro u v
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Hf, Matrix.of_apply, smul_eq_mul]
  have hcoe : ((u : ZMod p) = (v : ZMod p)) ↔ u = v :=
    ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
  by_cases h : u = v <;> simp [h, hcoe]


open Matrix Commons
variable {p : ℕ} [Fact (Nat.Prime p)]

theorem lower (hp4 : p % 4 = 1) :
    ((p:ℝ) - 1) / (2 * (Real.sqrt p + 1))
      ≤ Commons.paleyLocTheta p (Fact.out : Nat.Prime p).pos := by
  haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have := (Fact.out : Nat.Prime p).pos; exact_mod_cast this
  have hs0 : (0:ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsp : (0:ℝ) < Real.sqrt p + 1 := by linarith
  have hone : Commons.IsNonzeroSq (1 : ZMod p) := ⟨one_ne_zero, ⟨1, by ring⟩⟩
  haveI : Nonempty (Commons.PaleyLocV p) := ⟨⟨1, hone⟩⟩
  obtain ⟨P, hPpsd, hPval⟩ := sub_psd_entry (p := p) hp4 (-1) (by norm_num)
  obtain ⟨P', hP'psd, hP'val⟩ := sub_psd_entry (p := p) hp4 1 (by norm_num)
  set N : ℕ := Fintype.card (Commons.PaleyLocV p) with hNdef
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast Fintype.card_pos
  set c : ℝ := 1 / ((N:ℝ) * (Real.sqrt p + 1)) with hc
  have hc0 : 0 < c := by positivity
  set J : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ := Matrix.of (fun _ _ => (1:ℝ))
    with hJ
  set X : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ := c • (P + J) with hX
  have hXval : ∀ u v, X u v
      = c * (Real.sqrt p * (if u = v then (1:ℝ) else 0) + chi p ((u:ZMod p) - v) + 1) := by
    intro u v
    simp only [hX, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, hPval u v, hJ,
      Matrix.of_apply]
    ring
  have hXpsd : X.PosSemidef :=
    Matrix.PosSemidef.smul (Matrix.PosSemidef.add hPpsd allOnes_psd) (le_of_lt hc0)
  -- trace
  have hchi0 : ∀ u : Commons.PaleyLocV p, chi p ((u:ZMod p) - u) = 0 := by
    intro u; rw [sub_self]; exact chi_zero
  have htrX : X.trace = 1 := by
    have : ∀ u : Commons.PaleyLocV p, X u u = c * (Real.sqrt p + 1) := by
      intro u; rw [hXval u u, hchi0 u, if_pos rfl]; ring
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl fun u _ => this u, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hc, ← hNdef]
    field_simp
  -- zero pattern
  have hzero : ∀ u v : Commons.PaleyLocV p, u ≠ v → ¬ Commons.paleyLocAdj p u v → X u v = 0 := by
    intro u v huv hadj
    have hne : ((u : ZMod p) - v) ≠ 0 := by
      intro hc'
      exact huv (Subtype.ext (sub_eq_zero.mp hc'))
    have : chi p ((u:ZMod p) - v) = -1 := chi_notSq hne hadj
    rw [hXval u v, this, if_neg huv]
    ring
  -- the objective
  have hPval' : ∀ u v, P u v
      = Real.sqrt p * (if u = v then (1:ℝ) else 0) + chi p ((u:ZMod p) - v) := by
    intro u v; rw [hPval u v]; ring
  have hone_row : ∀ u : Commons.PaleyLocV p,
      ∑ v : Commons.PaleyLocV p, (if u = v then (1:ℝ) else 0) = 1 := by
    intro u; simp
  have hP1 : 0 ≤ ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, P u v := by
    have h := hPpsd.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
    have e : (fun _ => (1:ℝ)) ⬝ᵥ P.mulVec (fun _ => 1)
        = ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, P u v := by
      simp [dotProduct, Matrix.mulVec]
    simpa [e] using h
  have hPsum : ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, P u v
      = Real.sqrt p * (N:ℝ)
        + ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, chi p ((u:ZMod p) - v) := by
    have step : ∀ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, P u v
        = Real.sqrt p + ∑ v : Commons.PaleyLocV p, chi p ((u:ZMod p) - v) := by
      intro u
      rw [Finset.sum_congr rfl fun v _ => hPval' u v, Finset.sum_add_distrib, ← Finset.mul_sum,
        hone_row u, mul_one]
    rw [Finset.sum_congr rfl fun u _ => step u, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← hNdef]
    ring
  have hsigLB : -(Real.sqrt p * (N:ℝ))
      ≤ ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, chi p ((u:ZMod p) - v) := by
    rw [hPsum] at hP1; linarith
  have hSval : ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v
      = c * (Real.sqrt p * (N:ℝ)
        + (∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, chi p ((u:ZMod p) - v))
        + (N:ℝ) * (N:ℝ)) := by
    have step : ∀ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v
        = c * (Real.sqrt p + (∑ v : Commons.PaleyLocV p, chi p ((u:ZMod p) - v)) + (N:ℝ)) := by
      intro u
      rw [Finset.sum_congr rfl fun v _ => hXval u v, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hone_row u, mul_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← hNdef]
    rw [Finset.sum_congr rfl fun u _ => step u, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hNdef, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef]
    ring
  have hmem : (∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v)
      ∈ Commons.thetaCliqueFeasible (Commons.paleyLocAdj p) := ⟨X, hXpsd, htrX, hzero, rfl⟩
  have hle : (∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v)
      ≤ Commons.paleyLocTheta p (Fact.out : Nat.Prime p).pos := le_csSup (bdd hp4) hmem
  have hcNN : c * ((N:ℝ) * (N:ℝ)) = (N:ℝ) / (Real.sqrt p + 1) := by
    rw [hc]; field_simp
  have hobj : (N:ℝ) / (Real.sqrt p + 1)
      ≤ ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v := by
    rw [hSval, ← hcNN]
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc0)
  have hcard := card_eq (p := p) hp4
  have hNval : (N:ℝ) = ((p:ℝ) - 1) / 2 := by rw [← hNdef] at hcard; linarith
  have : ((p:ℝ) - 1) / (2 * (Real.sqrt p + 1)) = (N:ℝ) / (Real.sqrt p + 1) := by
    rw [hNval]; field_simp
  rw [this]
  linarith



/-- **The window.**  For every prime `p ≡ 1 (mod 4)`,
`(p-1)/(2(√p+1)) ≤ ϑ(Ḡ_{p,1}) ≤ 1 + √p`. -/
theorem proof :
    ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
      ((p : ℝ) - 1) / (2 * (Real.sqrt p + 1)) ≤ Commons.paleyLocTheta p hp.pos ∧
        Commons.paleyLocTheta p hp.pos ≤ 1 + Real.sqrt p := by
  intro p hp hp4
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ⟨lower hp4, upper hp4⟩

end Submissions.PaleyLocThetaWindow.ConferenceMatrixWindow
