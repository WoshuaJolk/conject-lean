import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Real Metric Set
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace Submissions.PlyUpperTwoPowSqrt.CapCylinder

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma sum_sq_iff (n : ℕ) (β : ℝ) (hβ : 0 ≤ β) (y : Fin n → ℝ) :
    (WithLp.toLp 2 y : E n) ∈ closedBall (0 : E n) β ↔ ∑ j, (y j)^2 ≤ β^2 := by
  have hS : (0:ℝ) ≤ ∑ j, (y j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  simp only [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have hrw : ∑ j, ‖(WithLp.toLp 2 y : E n) j‖^2 = ∑ j, (y j)^2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Real.norm_eq_abs, sq_abs]
  rw [hrw]
  constructor
  · intro h
    have := Real.sq_sqrt hS
    nlinarith [Real.sqrt_nonneg (∑ j, (y j)^2)]
  · intro h
    calc Real.sqrt (∑ j, (y j)^2) ≤ Real.sqrt (β^2) := Real.sqrt_le_sqrt h
      _ = β := Real.sqrt_sq hβ

lemma ball_pi (n : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    volume {y : Fin n → ℝ | ∑ j, (y j)^2 ≤ β^2} = volume (closedBall (0 : E n) β) := by
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → E n) ⁻¹' (closedBall (0 : E n) β)
      = {y : Fin n → ℝ | ∑ j, (y j)^2 ≤ β^2} := by
    ext y; exact sum_sq_iff n β hβ y
  rw [← hpre]
  exact (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet

lemma meas_pi (m : ℕ) (c1 c2 β : ℝ) :
    MeasurableSet {x : Fin (m+2) → ℝ |
      x 0 ∈ Set.Icc c1 c2 ∧ ∑ j : Fin (m+1), (x j.succ)^2 ≤ β^2} := by
  refine MeasurableSet.inter ((measurable_pi_apply (0 : Fin (m+2))) measurableSet_Icc) ?_
  have hm : Measurable fun x : Fin (m+2) → ℝ => ∑ j : Fin (m+1), (x j.succ)^2 := by
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact ((measurable_pi_apply j.succ).pow_const 2)
  exact hm measurableSet_Iic

lemma meas_E (m : ℕ) (c1 c2 β : ℝ) :
    MeasurableSet {v : E (m+2) |
      v 0 ∈ Set.Icc c1 c2 ∧ ∑ j : Fin (m+1), (v j.succ)^2 ≤ β^2} :=
  (PiLp.volume_preserving_ofLp (Fin (m+2))).measurable (meas_pi m c1 c2 β)

lemma cyl_volume (m : ℕ) (c1 c2 β : ℝ) (hβ : 0 ≤ β) :
    volume {w : E (m+2) | (w 0 ∈ Set.Icc c1 c2) ∧ ∑ j : Fin (m+1), (w j.succ)^2 ≤ β^2}
      = ENNReal.ofReal (c2 - c1) * volume (closedBall (0 : E (m+1)) β) := by
  classical
  set T : Set (Fin (m+1) → ℝ) := {y | ∑ j, (y j)^2 ≤ β^2} with hT
  set S : Set (Fin (m+2) → ℝ) :=
    {x | x 0 ∈ Set.Icc c1 c2 ∧ ∑ j : Fin (m+1), (x j.succ)^2 ≤ β^2} with hS
  have hTm : MeasurableSet T := by
    have : Measurable fun y : Fin (m+1) → ℝ => ∑ j, (y j)^2 := by
      refine Finset.measurable_sum _ (fun j _ => ?_)
      exact ((measurable_pi_apply j).pow_const 2)
    exact this measurableSet_Iic
  have hSm : MeasurableSet S := meas_pi m c1 c2 β
  have hSE : MeasurableSet {w : E (m+2) | (w 0 ∈ Set.Icc c1 c2) ∧
      ∑ j : Fin (m+1), (w j.succ)^2 ≤ β^2} := meas_E m c1 c2 β
  have h1 : volume {w : E (m+2) | (w 0 ∈ Set.Icc c1 c2) ∧
      ∑ j : Fin (m+1), (w j.succ)^2 ≤ β^2} = volume S := by
    rw [← (PiLp.volume_preserving_toLp (Fin (m+2))).measure_preimage hSE.nullMeasurableSet]
    rfl
  have hsplit : S = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+2) => ℝ) 0) ⁻¹'
      (Set.Icc c1 c2 ×ˢ T) := by
    ext x
    simp [hS, hT, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail, Set.mem_prod]
  have h2 : volume S = volume (Set.Icc c1 c2 ×ˢ T) := by
    rw [hsplit]
    exact (volume_preserving_piFinSuccAbove (fun _ : Fin (m+2) => ℝ) 0).measure_preimage
      ((measurableSet_Icc.prod hTm)).nullMeasurableSet
  rw [h1, h2, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    ← ball_pi (m+1) β hβ]

lemma exists_onb {d : ℕ} (hd : 1 ≤ d) (u : E d) (hu : ‖u‖ = 1) :
    ∃ (bs : OrthonormalBasis (Fin d) ℝ (E d)), bs ⟨0, hd⟩ = u := by
  classical
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  have hcard : Module.finrank ℝ (E d) = Fintype.card (Fin d) := by simp
  have horth : Orthonormal ℝ (({i0} : Set (Fin d)).domRestrict (fun _ : Fin d => u)) := by
    constructor
    · intro i; simpa using hu
    · intro i j hij
      exact absurd (Subtype.ext (by rw [i.2, j.2])) hij
  obtain ⟨bs, hbs⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨bs, hbs i0 rfl⟩

/-- Volume of the `u`-cylinder inside the unit ball. -/
lemma cyl_vol_u (m : ℕ) (h β : ℝ) (hβ : 0 ≤ β) (u : E (m+2)) (hu : ‖u‖ = 1) :
    volume {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (-(1/2)-h) (-(1/2)) ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2}
      = ENNReal.ofReal h * volume (closedBall (0 : E (m+1)) β) := by
  classical
  obtain ⟨bs, hbs⟩ := exists_onb (d := m+2) (by omega) u hu
  set Ψ : E (m+2) ≃ₗᵢ[ℝ] E (m+2) := bs.repr with hΨ
  have hΨu : Ψ u = EuclideanSpace.single (⟨0, by omega⟩ : Fin (m+2)) (1:ℝ) := by
    rw [hΨ, ← hbs, bs.repr_self]
  have hzero : (⟨0, by omega⟩ : Fin (m+2)) = 0 := rfl
  have hkey : ∀ w : E (m+2), ⟪u, w⟫ = (Ψ w) 0 := by
    intro w
    have := Ψ.inner_map_map u w
    rw [hΨu, hzero] at this
    rw [← this]
    simp [EuclideanSpace.inner_single_left]
  have hnorm : ∀ w : E (m+2), ‖w‖ = ‖Ψ w‖ := fun w => (Ψ.norm_map w).symm
  have hsplit : ∀ v : E (m+2), ‖v‖^2 - (v 0)^2 = ∑ j : Fin (m+1), (v j.succ)^2 := by
    intro v
    have hn : ‖v‖^2 = ∑ i : Fin (m+2), (v i)^2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      exact Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
    rw [hn, Fin.sum_univ_succ]
    ring
  have hpre : {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (-(1/2)-h) (-(1/2)) ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2}
      = Ψ ⁻¹' {v : E (m+2) | (v 0 ∈ Set.Icc (-(1/2)-h) (-(1/2))) ∧
          ∑ j : Fin (m+1), (v j.succ)^2 ≤ β^2} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hkey w, ← hsplit (Ψ w), ← hnorm w]
  rw [hpre, (Ψ.measurePreserving).measure_preimage
      (meas_E m (-(1/2)-h) (-(1/2)) β).nullMeasurableSet,
    cyl_volume m (-(1/2)-h) (-(1/2)) β hβ]
  congr 2
  ring

lemma exists_unit {d : ℕ} (hd : 1 ≤ d) (p : E d) : ∃ u : E d, ‖u‖ = 1 ∧ p = ‖p‖ • u := by
  by_cases hp : p = 0
  · exact ⟨EuclideanSpace.single ⟨0, hd⟩ (1:ℝ), by simp [EuclideanSpace.norm_single], by simp [hp]⟩
  · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    refine ⟨‖p‖⁻¹ • p, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖p‖⁻¹)]
      field_simp
    · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

lemma cyl_subset (m : ℕ) {h β : ℝ} (hh : 0 ≤ h) (hβ2 : β^2 = 1 - (1/2+h)^2)
    {p u : E (m+2)} (hu : ‖u‖ = 1) (hpu : p = ‖p‖ • u) (hp : ‖p‖ ≤ 2) :
    (fun w : E (m+2) => p + w) ''
        {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (-(1/2)-h) (-(1/2)) ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2}
      ⊆ closedBall p 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3) := by
  rintro z ⟨w, ⟨⟨hw1, hw2⟩, hw3⟩, rfl⟩
  have hnw : ‖w‖^2 ≤ 1 := by nlinarith
  have hnw1 : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
  constructor
  · simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hnw1
  · have hpw : ⟪p, w⟫ = ‖p‖ * ⟪u, w⟫ := by rw [hpu, real_inner_smul_left, ← hpu]
    have hs0 : (0:ℝ) ≤ ‖p‖ := norm_nonneg p
    have h3 : ‖p + w‖^2 ≤ 3 := by
      rw [norm_add_sq_real, hpw]
      nlinarith
    have := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_sq (norm_nonneg _)] at this
    simpa [mem_closedBall, dist_eq_norm] using this

lemma lens_vol_lower (m : ℕ) {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 ≤ β)
    (hβ2 : β^2 = 1 - (1/2+h)^2) (p : E (m+2)) (hp : ‖p‖ ≤ 2) :
    ENNReal.ofReal h * volume (closedBall (0 : E (m+1)) β)
      ≤ volume (closedBall p 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) := by
  obtain ⟨u, hu, hpu⟩ := exists_unit (d := m+2) (by omega) p
  set C : Set (E (m+2)) :=
    {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (-(1/2)-h) (-(1/2)) ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2} with hC
  have htr : volume ((fun w : E (m+2) => p + w) '' C) = volume C := by
    rw [Set.image_add_left]
    exact measure_preimage_add volume (-p) C
  calc ENNReal.ofReal h * volume (closedBall (0 : E (m+1)) β)
      = volume C := (cyl_vol_u m h β hβ u hu).symm
    _ = volume ((fun w : E (m+2) => p + w) '' C) := htr.symm
    _ ≤ volume (closedBall p 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) :=
        measure_mono (cyl_subset m hh hβ2 hu hpu hp)

/-- Volume of the unit ball of `E n`, as a real number. -/
def vb (n : ℕ) : ℝ := (volume (closedBall (0 : E n) 1)).toReal

lemma vb_pos (n : ℕ) : 0 < vb n :=
  ENNReal.toReal_pos (ne_of_gt (measure_closedBall_pos volume 0 one_pos))
    (ne_of_lt measure_closedBall_lt_top)

lemma vol_ball_eq (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (closedBall (0 : E n) r) = ENNReal.ofReal (r ^ n) * ENNReal.ofReal (vb n) := by
  rw [Measure.addHaar_closedBall' volume (0 : E n) hr]
  congr 1
  · congr 1; simp
  · rw [vb, ENNReal.ofReal_toReal (ne_of_lt measure_closedBall_lt_top)]

lemma count_sum_le {d N k : ℕ} (q : Fin N → E d) (W : Set (E d))
    (hthin : ∀ y : E d, {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) :
    ∑ j : Fin N, volume (closedBall (q j) 1 ∩ W) ≤ (k : ℝ≥0∞) * volume W := by
  classical
  have hkey : ∀ j : Fin N, volume (closedBall (q j) 1 ∩ W)
      = ∫⁻ y in W, (closedBall (q j) 1).indicator (fun _ => (1:ℝ≥0∞)) y := by
    intro j
    rw [lintegral_indicator measurableSet_closedBall, setLIntegral_one,
      Measure.restrict_apply measurableSet_closedBall]
  have hmeas : ∀ j : Fin N,
      Measurable ((closedBall (q j) 1).indicator (fun _ => (1:ℝ≥0∞))) :=
    fun j => (measurable_const.indicator measurableSet_closedBall)
  have hpt : ∀ y : E d,
      ∑ j : Fin N, (closedBall (q j) 1).indicator (fun _ => (1:ℝ≥0∞)) y ≤ (k : ℝ≥0∞) := by
    intro y
    have hset : {j : Fin N | dist y (q j) ≤ 1}.toFinset
        = Finset.univ.filter (fun j => dist y (q j) ≤ 1) := by ext j; simp
    have hcard : (Finset.univ.filter (fun j : Fin N => dist y (q j) ≤ 1)).card ≤ k := by
      rw [← hset, ← Set.ncard_eq_toFinset_card']; exact hthin y
    have hrw : ∑ j : Fin N, (closedBall (q j) 1).indicator (fun _ => (1:ℝ≥0∞)) y
        = ((Finset.univ.filter (fun j : Fin N => dist y (q j) ≤ 1)).card : ℝ≥0∞) := by
      simp only [Set.indicator_apply, Metric.mem_closedBall]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        mul_one]
    rw [hrw]
    exact_mod_cast hcard
  calc ∑ j : Fin N, volume (closedBall (q j) 1 ∩ W)
      = ∑ j : Fin N, ∫⁻ y in W, (closedBall (q j) 1).indicator (fun _ => (1:ℝ≥0∞)) y :=
        Finset.sum_congr rfl (fun j _ => hkey j)
    _ = ∫⁻ y in W, ∑ j : Fin N, (closedBall (q j) 1).indicator (fun _ => (1:ℝ≥0∞)) y := by
        rw [lintegral_finsetSum _ (fun j _ => (hmeas j))]
    _ ≤ ∫⁻ _ in W, (k : ℝ≥0∞) := lintegral_mono (fun y => hpt y)
    _ = (k : ℝ≥0∞) * volume W := by rw [setLIntegral_const]

theorem packing_le2 (m : ℕ) {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 ≤ β)
    (hβ2 : β^2 = 1 - (1/2+h)^2) (N k : ℕ) (q : Fin N → E (m+2))
    (hq : ∀ j, ‖q j‖ ≤ 2)
    (hthin : ∀ y : E (m+2), {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) :
    (N : ℝ) * (h * β^(m+1) * vb (m+1)) ≤ (k : ℝ) * ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
  have hlow : ∀ j : Fin N,
      ENNReal.ofReal (h * β^(m+1) * vb (m+1))
        ≤ volume (closedBall (q j) 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) := by
    intro j
    have := lens_vol_lower m hh hβ hβ2 (q j) (hq j)
    refine le_trans (le_of_eq ?_) this
    rw [vol_ball_eq (m+1) β hβ, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ h * β^(m+1)),
      ENNReal.ofReal_mul hh, mul_assoc]
  have hsum1 : (N : ℝ≥0∞) * ENNReal.ofReal (h * β^(m+1) * vb (m+1))
      ≤ ∑ j : Fin N, volume (closedBall (q j) 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hlow j)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hsum2 := count_sum_le q (closedBall (0 : E (m+2)) (Real.sqrt 3)) hthin
  have hW : volume (closedBall (0 : E (m+2)) (Real.sqrt 3))
      = ENNReal.ofReal ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
    rw [vol_ball_eq (m+2) _ (Real.sqrt_nonneg 3), ENNReal.ofReal_mul (by positivity)]
  have hchain : (N : ℝ≥0∞) * ENNReal.ofReal (h * β^(m+1) * vb (m+1))
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
    calc (N : ℝ≥0∞) * ENNReal.ofReal (h * β^(m+1) * vb (m+1))
        ≤ ∑ j : Fin N, volume (closedBall (q j) 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) :=
          hsum1
      _ ≤ (k : ℝ≥0∞) * volume (closedBall (0 : E (m+2)) (Real.sqrt 3)) := hsum2
      _ = (k : ℝ≥0∞) * ENNReal.ofReal ((Real.sqrt 3)^(m+2) * vb (m+2)) := by rw [hW]
  rw [show ((N:ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp,
      show ((k:ℕ) : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) by simp,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hchain
  have hnn : (0:ℝ) ≤ (k : ℝ) * ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
    have := (vb_pos (m+2)).le; positivity
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hchain

lemma gamma_half_le (x : ℝ) (hx : 0 < x) :
    Real.Gamma (x + 1/2) * Real.sqrt x ≤ Real.Gamma (x + 1) := by
  have hgx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hgx1 : 0 < Real.Gamma (x+1) := Real.Gamma_pos_of_pos (by linarith)
  have h1 := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x+1)
      hx (by linarith) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  rw [show (1/2 : ℝ)*x + (1/2)*(x+1) = x + 1/2 by ring,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hgx.le] at h1
  have hprod : Real.Gamma x * Real.Gamma (x+1) = (Real.Gamma (x+1))^2 / x := by
    rw [Real.Gamma_add_one (ne_of_gt hx)]; field_simp
  rw [hprod, Real.sqrt_div (by positivity), Real.sqrt_sq hgx1.le,
    le_div_iff₀ (Real.sqrt_pos.mpr hx)] at h1
  exact h1

lemma vb_eq (n : ℕ) (hn : 1 ≤ n) : vb n = Real.sqrt π ^ n / Real.Gamma ((n:ℝ)/2 + 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := EuclideanSpace.volume_closedBall (Fin n) (0 : E n) 1
  rw [vb, h]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal]
  positivity

lemma vb_ratio (m : ℕ) : Real.sqrt (((m:ℝ)+2)/(2*π)) * vb (m+2) ≤ vb (m+1) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set x : ℝ := ((m:ℝ)+2)/2 with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hg := gamma_half_le x hx0
  have hgx1 : 0 < Real.Gamma (x+1) := Real.Gamma_pos_of_pos (by linarith)
  have hgxh : 0 < Real.Gamma (x+1/2) := Real.Gamma_pos_of_pos (by linarith)
  have e1 : vb (m+2) = Real.sqrt π ^ (m+2) / Real.Gamma (x+1) := by
    rw [vb_eq (m+2) (by omega)]
    congr 2
    push_cast [hx]
    ring
  have e2 : vb (m+1) = Real.sqrt π ^ (m+1) / Real.Gamma (x+1/2) := by
    rw [vb_eq (m+1) (by omega)]
    congr 2
    push_cast [hx]
    ring
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hpi
  have hsqrt : Real.sqrt (((m:ℝ)+2)/(2*π)) = Real.sqrt x / Real.sqrt π := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    rw [hx]; field_simp
  rw [e1, e2, hsqrt]
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hgxh]
  have hpow : Real.sqrt x * Real.sqrt π ^ (m+2) = Real.sqrt π * (Real.sqrt x * Real.sqrt π ^ (m+1)) := by
    ring
  calc Real.sqrt x * Real.sqrt π ^ (m + 2) * Real.Gamma (x + 1/2)
      = Real.sqrt π ^ (m+1) * Real.sqrt π * (Real.Gamma (x+1/2) * Real.sqrt x) := by ring
    _ ≤ Real.sqrt π ^ (m+1) * Real.sqrt π * Real.Gamma (x+1) := by
        have : (0:ℝ) ≤ Real.sqrt π ^ (m+1) * Real.sqrt π := by positivity
        exact mul_le_mul_of_nonneg_left hg this
    _ = Real.sqrt π ^ (m+1) * (Real.sqrt π * Real.Gamma (x+1)) := by ring

lemma arith_key2 (m : ℕ) :
    ∃ h β : ℝ, 0 < h ∧ 0 < β ∧ β^2 = 1 - (1/2+h)^2 ∧
      (Real.sqrt 3)^(m+2) ≤ (100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) *
        (h * β^(m+1) * Real.sqrt (((m:ℝ)+2)/(2*π))) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set M : ℝ := (m : ℝ) with hM
  clear_value M
  have hM0 : (0:ℝ) ≤ M := by rw [hM]; exact Nat.cast_nonneg m
  have hden : (0:ℝ) < M + 10 := by linarith
  set h : ℝ := 1/(M+10) with hh_def
  clear_value h
  have hh : 0 < h := by rw [hh_def]; positivity
  have hh10 : h ≤ 1/10 := by
    rw [hh_def]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  set z : ℝ := (4/3)*(h + h^2) with hz_def
  clear_value z
  have hz0 : 0 < z := by rw [hz_def]; positivity
  have hz2 : z ≤ 1/2 := by rw [hz_def]; nlinarith
  set B2 : ℝ := 1 - (1/2+h)^2 with hB2_def
  clear_value B2
  have hB2z : B2 = (3/4) * (1 - z) := by rw [hB2_def, hz_def]; ring
  have hB2pos : 0 < B2 := by rw [hB2z]; nlinarith
  set β : ℝ := Real.sqrt B2 with hβ_def
  clear_value β
  have hβ : 0 < β := by rw [hβ_def]; exact Real.sqrt_pos.mpr hB2pos
  have hβsq : β^2 = B2 := by rw [hβ_def]; exact Real.sq_sqrt hB2pos.le
  refine ⟨h, β, hh, hβ, by rw [hβsq, hB2_def], ?_⟩
  -- exponential lower bound on (1 - z)
  have hexpz : Real.exp (-(2*z)) ≤ 1 - z := by
    have he : (1:ℝ) + 2*z ≤ Real.exp (2*z) := by
      have := Real.add_one_le_exp (2*z); linarith
    have hpos : (0:ℝ) < 1 + 2*z := by linarith
    have h2 : Real.exp (-(2*z)) ≤ (1+2*z)⁻¹ := by
      rw [Real.exp_neg]; exact inv_anti₀ hpos he
    have h3 : (1+2*z)⁻¹ ≤ 1 - z := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]; nlinarith
    linarith
  have hzm : 2*z*(M+1) ≤ 5 := by
    have h1 : h * (M+1) ≤ 1 := by
      rw [hh_def]; rw [div_mul_eq_mul_div, div_le_one hden]; linarith
    have h2 : h^2 * (M+1) ≤ 1/10 := by nlinarith
    rw [hz_def]; nlinarith
  have hB2m : (3/4:ℝ)^(m+1) * Real.exp (-5) ≤ B2^(m+1) := by
    have hstep1 : Real.exp (-(2*z)) ^ (m+1) ≤ (1 - z)^(m+1) :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hexpz (m+1)
    have hstep2 : Real.exp (-(2*z)) ^ (m+1) = Real.exp (((m:ℝ)+1) * (-(2*z))) := by
      rw [show ((m:ℝ)+1) = ((m+1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul]
    have hstep3 : Real.exp (-5) ≤ Real.exp (((m:ℝ)+1) * (-(2*z))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hzm]
    have hfin : Real.exp (-5) ≤ (1-z)^(m+1) := by rw [hstep2] at hstep1; linarith
    calc (3/4:ℝ)^(m+1) * Real.exp (-5) ≤ (3/4:ℝ)^(m+1) * (1-z)^(m+1) := by
          have hnn : (0:ℝ) ≤ (3/4:ℝ)^(m+1) := by positivity
          nlinarith
      _ = B2^(m+1) := by rw [hB2z, mul_pow]
  have hMh : (1:ℝ)/5 ≤ (M+2)*h := by
    rw [hh_def, mul_one_div, le_div_iff₀ hden]; linarith
  have hMh2 : (1:ℝ)/25 ≤ ((M+2)*h)^2 := by nlinarith
  -- squares
  set Y : ℝ := (100 * Real.exp 5) * 2^(m+2) * Real.sqrt (M+2) *
      (h * β^(m+1) * Real.sqrt ((M+2)/(2*π))) with hY_def
  clear_value Y
  have hM2 : (0:ℝ) < M + 2 := by linarith
  have hYnn : 0 ≤ Y := by
    rw [hY_def]
    have := Real.exp_pos (5:ℝ)
    have h1 : (0:ℝ) ≤ Real.sqrt (M+2) := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ Real.sqrt ((M+2)/(2*π)) := Real.sqrt_nonneg _
    positivity
  have hsq1 : (Real.sqrt (M+2))^2 = M+2 := Real.sq_sqrt hM2.le
  have hsq2 : (Real.sqrt ((M+2)/(2*π)))^2 = (M+2)/(2*π) := Real.sq_sqrt (by positivity)
  have hb2m : (β^(m+1))^2 = B2^(m+1) := by rw [← pow_mul, mul_comm, pow_mul, hβsq]
  have h2m : ((2:ℝ)^(m+2))^2 = 4^(m+2) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hY2 : Y^2 = (100 * Real.exp 5)^2 * ((M+2)*h)^2 * (4^(m+2) * B2^(m+1)) / (2*π) := by
    rw [hY_def]
    rw [show ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt (M+2) *
        (h * β^(m+1) * Real.sqrt ((M+2)/(2*π))))^2
        = (100 * Real.exp 5)^2 * (h^2 * (Real.sqrt (M+2))^2 * (Real.sqrt ((M+2)/(2*π)))^2)
          * (((2:ℝ)^(m+2))^2 * (β^(m+1))^2) by ring, hsq1, hsq2, hb2m, h2m]
    field_simp
  have hexp1 : (1:ℝ) ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
  have hlow : (100 * Real.exp 5)^2 * (1/25) * (4^(m+2) * ((3/4:ℝ)^(m+1) * Real.exp (-5))) / (2*π)
      ≤ Y^2 := by
    rw [hY2]
    have h4 : (0:ℝ) < (4:ℝ)^(m+2) := by positivity
    gcongr
  have hsimp : (100 * Real.exp 5)^2 * (1/25) *
      ((4:ℝ)^(m+2) * ((3/4:ℝ)^(m+1) * Real.exp (-5))) / (2*π)
      = (1600 * Real.exp 5 / (2*π)) * 3^(m+1) := by
    have hE : (Real.exp 5)^2 * Real.exp (-5) = Real.exp 5 := by
      rw [Real.exp_neg, sq]; field_simp
    have h43 : (4:ℝ)^(m+2) * (3/4:ℝ)^(m+1) = 4 * 3^(m+1) := by
      rw [pow_succ, mul_comm ((4:ℝ)^(m+1)) 4, mul_assoc, ← mul_pow]
      norm_num
    calc (100 * Real.exp 5)^2 * (1/25) *
          ((4:ℝ)^(m+2) * ((3/4:ℝ)^(m+1) * Real.exp (-5))) / (2*π)
        = (400 * ((Real.exp 5)^2 * Real.exp (-5)) * ((4:ℝ)^(m+2) * (3/4:ℝ)^(m+1))) / (2*π) := by
          ring
      _ = (400 * Real.exp 5 * (4 * 3^(m+1))) / (2*π) := by rw [hE, h43]
      _ = (1600 * Real.exp 5 / (2*π)) * 3^(m+1) := by ring
  have hX2 : ((Real.sqrt 3)^(m+2))^2 = (3:ℝ)^(m+2) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have h3m : (0:ℝ) < 3^(m+1) := by positivity
  have hgoal : (3:ℝ)^(m+2) ≤ (1600 * Real.exp 5 / (2*π)) * 3^(m+1) := by
    rw [pow_succ]
    have hpib : π ≤ 4 := Real.pi_le_four
    have h1 : (3:ℝ) ≤ 1600 * Real.exp 5 / (2*π) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc (3:ℝ)^(m+1) * 3 ≤ 3^(m+1) * (1600 * Real.exp 5 / (2*π)) :=
          mul_le_mul_of_nonneg_left h1 h3m.le
      _ = (1600 * Real.exp 5 / (2*π)) * 3^(m+1) := by ring
  have hfinal : ((Real.sqrt 3)^(m+2))^2 ≤ Y^2 := by
    rw [hX2]
    calc (3:ℝ)^(m+2) ≤ (1600 * Real.exp 5 / (2*π)) * 3^(m+1) := hgoal
      _ = (100 * Real.exp 5)^2 * (1/25) *
          ((4:ℝ)^(m+2) * ((3/4:ℝ)^(m+1) * Real.exp (-5))) / (2*π) := hsimp.symm
      _ ≤ Y^2 := hlow
  have := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hYnn] at this

theorem packing_bound (m N k : ℕ) (q : Fin N → E (m+2)) (hq : ∀ j, ‖q j‖ ≤ 2)
    (hthin : ∀ y : E (m+2), {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) :
    (N : ℝ) ≤ (100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k := by
  obtain ⟨h, β, hh, hβ, hβ2, hineq⟩ := arith_key2 m
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hM2 : (0:ℝ) < (m:ℝ)+2 := by positivity
  set S : ℝ := Real.sqrt (((m:ℝ)+2)/(2*π)) with hS_def
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  set P : ℝ := h * β^(m+1) with hP_def
  have hP : 0 < P := by rw [hP_def]; positivity
  have hV1 : 0 < vb (m+1) := vb_pos (m+1)
  have hV2 : 0 < vb (m+2) := vb_pos (m+2)
  have hp := packing_le2 m hh.le hβ.le hβ2 N k q hq hthin
  have hr := vb_ratio m
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hstep : (N:ℝ) * (P * S) * vb (m+2) ≤ (k:ℝ) * (Real.sqrt 3)^(m+2) * vb (m+2) := by
    have hSV : S * vb (m+2) ≤ vb (m+1) := by rw [hS_def]; exact hr
    have h1 : (N:ℝ) * (P * (S * vb (m+2))) ≤ (N:ℝ) * (P * vb (m+1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSV hP.le) hN0
    calc (N:ℝ) * (P * S) * vb (m+2) = (N:ℝ) * (P * (S * vb (m+2))) := by ring
      _ ≤ (N:ℝ) * (P * vb (m+1)) := h1
      _ = (N:ℝ) * (h * β^(m+1) * vb (m+1)) := by rw [hP_def]
      _ ≤ (k:ℝ) * ((Real.sqrt 3)^(m+2) * vb (m+2)) := hp
      _ = (k:ℝ) * (Real.sqrt 3)^(m+2) * vb (m+2) := by ring
  have hcancel : (N:ℝ) * (P * S) ≤ (k:ℝ) * (Real.sqrt 3)^(m+2) :=
    le_of_mul_le_mul_right hstep hV2
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hup : (k:ℝ) * (Real.sqrt 3)^(m+2)
      ≤ ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k) * (P * S) := by
    have := mul_le_mul_of_nonneg_left hineq hk0
    calc (k:ℝ) * (Real.sqrt 3)^(m+2)
        ≤ (k:ℝ) * ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * (h * β^(m+1) * S)) :=
          this
      _ = ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k) * (P * S) := by
          rw [hP_def]; ring
  have hfin : (N:ℝ) * (P * S)
      ≤ ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k) * (P * S) := by
    linarith [hcancel, hup]
  exact le_of_mul_le_mul_right hfin (by positivity)

/-- In dimension one the reduced problem needs only a two-ball cover. -/
theorem packing_bound_one (N k : ℕ) (q : Fin N → E 1) (hq : ∀ j, ‖q j‖ ≤ 2)
    (hthin : ∀ y : E 1, {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) :
    (N : ℝ) ≤ 2 * k := by
  classical
  have hnorm : ∀ v : E 1, ‖v‖ = |v 0| := by
    intro v
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq_eq_abs, abs_abs]
  set y1 : E 1 := EuclideanSpace.single 0 (1:ℝ) with hy1
  set y2 : E 1 := EuclideanSpace.single 0 (-1:ℝ) with hy2
  have hcover : (Set.univ : Set (Fin N))
      ⊆ {j : Fin N | dist y1 (q j) ≤ 1} ∪ {j : Fin N | dist y2 (q j) ≤ 1} := by
    intro j _
    have hqj : |(q j) 0| ≤ 2 := by rw [← hnorm]; exact hq j
    rcases le_or_gt 0 ((q j) 0) with hpos | hneg
    · left
      simp only [Set.mem_setOf_eq, dist_eq_norm, hnorm]
      have : (y1 - q j) 0 = 1 - (q j) 0 := by simp [hy1, EuclideanSpace.single_apply]
      rw [this]
      rw [abs_le] at hqj ⊢
      constructor <;> linarith [hqj.1, hqj.2]
    · right
      simp only [Set.mem_setOf_eq, dist_eq_norm, hnorm]
      have : (y2 - q j) 0 = -1 - (q j) 0 := by simp [hy2, EuclideanSpace.single_apply]
      rw [this]
      rw [abs_le] at hqj ⊢
      constructor <;> linarith [hqj.1, hqj.2]
  have hcard : (Set.univ : Set (Fin N)).ncard ≤ k + k := by
    calc (Set.univ : Set (Fin N)).ncard
        ≤ ({j : Fin N | dist y1 (q j) ≤ 1} ∪ {j : Fin N | dist y2 (q j) ≤ 1}).ncard :=
          Set.ncard_le_ncard hcover (Set.toFinite _)
      _ ≤ {j : Fin N | dist y1 (q j) ≤ 1}.ncard + {j : Fin N | dist y2 (q j) ≤ 1}.ncard :=
          Set.ncard_union_le _ _
      _ ≤ k + k := Nat.add_le_add (hthin y1) (hthin y2)
  have huniv : (Set.univ : Set (Fin N)).ncard = N := by simp
  rw [huniv] at hcard
  have : (N : ℝ) ≤ ((k + k : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at this
  linarith

-- === min-radius reduction ===


/-- Du–McCarty's sub-ball: inside `closedBall a R`, the ball of the smaller radius `r₀`
pushed as far as possible toward `b`. -/
def sub (a b : E d) (R r₀ : ℝ) : E d :=
  if ‖b - a‖ = 0 then a
  else a + (min (R - r₀) ‖b - a‖ / ‖b - a‖) • (b - a)

lemma sub_dist_a (a b : E d) {R r₀ : ℝ} (hR : r₀ ≤ R) :
    ‖sub a b R r₀ - a‖ ≤ R - r₀ := by
  unfold sub
  split_ifs with h
  · simp; linarith
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (le_min (by linarith) (norm_nonneg _)), abs_of_nonneg (norm_nonneg _),
      div_mul_cancel₀ _ h]
    exact min_le_left _ _

lemma sub_dist_b (a b : E d) {R r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hR : r₀ ≤ R)
    (hab : ‖b - a‖ ≤ R + r₀) : ‖sub a b R r₀ - b‖ ≤ 2 * r₀ := by
  unfold sub
  split_ifs with h
  · have hba : b = a := sub_eq_zero.mp (norm_eq_zero.mp h)
    rw [hba]; simp; linarith
  · have hpos : 0 < ‖b - a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    set s := min (R - r₀) ‖b - a‖ / ‖b - a‖ with hs
    have hs0 : 0 ≤ s := div_nonneg (le_min (by linarith) (norm_nonneg _)) (norm_nonneg _)
    have hs1 : s ≤ 1 := by rw [hs, div_le_one hpos]; exact min_le_right _ _
    have hrw : a + s • (b - a) - b = (1 - s) • (a - b) := by rw [sub_smul, one_smul]; module
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s),
      ← norm_neg (a - b), neg_sub]
    have hsn : s * ‖b - a‖ = min (R - r₀) ‖b - a‖ := by
      rw [hs, div_mul_cancel₀ _ (ne_of_gt hpos)]
    have hexp : (1 - s) * ‖b - a‖ = ‖b - a‖ - min (R - r₀) ‖b - a‖ := by
      rw [sub_mul, one_mul, hsn]
    rcases min_cases (R - r₀) ‖b - a‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [hexp, he] <;> linarith

lemma sub_ball_subset (a b : E d) {R r₀ : ℝ} (hR : r₀ ≤ R) :
    closedBall (sub a b R r₀) r₀ ⊆ closedBall a R := by
  intro z hz
  have h1 : ‖z - sub a b R r₀‖ ≤ r₀ := by simpa [dist_eq_norm] using hz
  have h2 : ‖sub a b R r₀ - a‖ ≤ R - r₀ := sub_dist_a a b hR
  have h3 : dist z a ≤ dist z (sub a b R r₀) + dist (sub a b R r₀) a := dist_triangle _ _ _
  simp only [dist_eq_norm] at h3
  simp only [mem_closedBall, dist_eq_norm]
  linarith



/-- **Du–McCarty's min-radius reduction.** If the reduced packing problem — unit balls with
centres in the closed ball of radius `2`, no point covered more than `k` times — is bounded by
`M`, then every finite `k`-thin collection of balls of positive radius in `ℝ^d` contains a ball
whose degree in the intersection graph is at most `M`. -/
theorem degree_le {d n k : ℕ} (hn : 0 < n)
    (x : Fin n → E d) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hthin : ∀ p : E d, {i : Fin n | p ∈ closedBall (x i) (r i)}.ncard ≤ k)
    (M : ℝ)
    (hM : ∀ (N : ℕ) (q : Fin N → E d), (∀ j, ‖q j‖ ≤ 2) →
            (∀ y : E d, {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) → (N : ℝ) ≤ M) :
    ∃ i₀ : Fin n,
      ({i : Fin n | i ≠ i₀ ∧
        (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty}.ncard : ℝ) ≤ M := by
  classical
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin n)) r ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  set r₀ := r i₀ with hr₀def
  have hr₀ : 0 < r₀ := hr i₀
  set S : Set (Fin n) :=
    {i : Fin n | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty} with hS
  set T : Finset (Fin n) := S.toFinset with hT
  have hcard : S.ncard = T.card := Set.ncard_eq_toFinset_card' S
  set e : Fin T.card ≃ {a // a ∈ T} := T.equivFin.symm with he
  -- the reduced configuration
  set idx : Fin T.card → Fin n := fun j => (e j : Fin n) with hidx
  have hidx_mem : ∀ j, idx j ∈ S := by
    intro j; exact Set.mem_toFinset.mp (e j).2
  have hle : ∀ j, r₀ ≤ r (idx j) := fun j => hmin _ (Finset.mem_univ _)
  have hdist : ∀ j, ‖x i₀ - x (idx j)‖ ≤ r (idx j) + r₀ := by
    intro j
    obtain ⟨z, hz1, hz2⟩ := (hidx_mem j).2
    have h1 : dist (x i₀) z ≤ r₀ := by rw [dist_comm]; exact hz2
    have h2 : dist z (x (idx j)) ≤ r (idx j) := hz1
    have := dist_triangle (x i₀) z (x (idx j))
    rw [dist_eq_norm] at this
    linarith
  set q : Fin T.card → E d :=
    fun j => r₀⁻¹ • (sub (x (idx j)) (x i₀) (r (idx j)) r₀ - x i₀) with hq
  have hqnorm : ∀ j, ‖q j‖ ≤ 2 := by
    intro j
    rw [hq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ r₀⁻¹)]
    have := sub_dist_b (x (idx j)) (x i₀) hr₀.le (hle j) (hdist j)
    rw [inv_mul_le_iff₀ hr₀]
    linarith
  have hqthin : ∀ y : E d, {j : Fin T.card | dist y (q j) ≤ 1}.ncard ≤ k := by
    intro y
    set z : E d := x i₀ + r₀ • y with hz
    have hmaps : ∀ j ∈ {j : Fin T.card | dist y (q j) ≤ 1},
        idx j ∈ {i : Fin n | z ∈ closedBall (x i) (r i)} := by
      intro j hj
      have hj' : dist y (q j) ≤ 1 := hj
      have hscale : ‖z - sub (x (idx j)) (x i₀) (r (idx j)) r₀‖ ≤ r₀ := by
        have hrw : z - sub (x (idx j)) (x i₀) (r (idx j)) r₀ = r₀ • (y - q j) := by
          rw [hz, hq, smul_sub, smul_inv_smul₀ (ne_of_gt hr₀)]; abel
        rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr₀.le]
        rw [dist_eq_norm] at hj'
        nlinarith [norm_nonneg (y - q j)]
      have : z ∈ closedBall (sub (x (idx j)) (x i₀) (r (idx j)) r₀) r₀ := by
        simpa [mem_closedBall, dist_eq_norm] using hscale
      exact sub_ball_subset (x (idx j)) (x i₀) (hle j) this
    have hinj : Set.InjOn idx {j : Fin T.card | dist y (q j) ≤ 1} := by
      intro a _ b _ hab
      have : (e a : Fin n) = (e b : Fin n) := hab
      exact e.injective (Subtype.ext this)
    calc {j : Fin T.card | dist y (q j) ≤ 1}.ncard
        ≤ {i : Fin n | z ∈ closedBall (x i) (r i)}.ncard :=
          Set.ncard_le_ncard_of_injOn idx hmaps hinj (Set.toFinite _)
      _ ≤ k := hthin z
  have := hM T.card q hqnorm hqthin
  rw [hcard]
  exact this



/-- The submitted proof of `Statements.PlyUpperTwoPowSqrt.statement`. -/
theorem proof :
    ∃ K : ℝ,
      ∀ d : ℕ, 1 ≤ d → ∃ C : ℕ,
        ∀ (k n : ℕ), 0 < n →
          ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
            (∀ i, 0 < r i) →
            Function.Injective (fun i => (x i, r i)) →
            (∀ p : EuclideanSpace ℝ (Fin d),
                {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
            ∃ i₀ : Fin n,
              ({i : Fin n | i ≠ i₀ ∧
                  (Metric.closedBall (x i) (r i) ∩
                    Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard : ℝ)
                ≤ K * 2 ^ d * Real.sqrt d * k + C := by
  refine ⟨100 * Real.exp 5, ?_⟩
  intro d hd
  refine ⟨0, ?_⟩
  intro k n hn x r hr _hinj hthin
  have hK : (2:ℝ) ≤ 100 * Real.exp 5 := by
    have := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 5); nlinarith
  match d, hd with
  | 1, _ =>
    have hM : ∀ (N : ℕ) (q : Fin N → E 1), (∀ j, ‖q j‖ ≤ 2) →
        (∀ y : E 1, {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) →
        (N : ℝ) ≤ (100 * Real.exp 5) * 2 ^ (1:ℕ) * Real.sqrt ((1:ℕ):ℝ) * k + (0:ℕ) := by
      intro N q h1 h2
      have := packing_bound_one N k q h1 h2
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      simp only [Nat.cast_one, Real.sqrt_one, mul_one, Nat.cast_zero, add_zero, pow_one]
      nlinarith
    obtain ⟨i₀, hi₀⟩ := degree_le hn x r hr hthin _ hM
    exact ⟨i₀, hi₀⟩
  | (m+2), _ =>
    have hM : ∀ (N : ℕ) (q : Fin N → E (m+2)), (∀ j, ‖q j‖ ≤ 2) →
        (∀ y : E (m+2), {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) →
        (N : ℝ) ≤ (100 * Real.exp 5) * 2 ^ (m+2) * Real.sqrt (((m+2:ℕ)):ℝ) * k + (0:ℕ) := by
      intro N q h1 h2
      have := packing_bound m N k q h1 h2
      have hc : (((m+2:ℕ)):ℝ) = (m:ℝ) + 2 := by push_cast; ring
      rw [hc, Nat.cast_zero, add_zero]
      exact this
    obtain ⟨i₀, hi₀⟩ := degree_le hn x r hr hthin _ hM
    exact ⟨i₀, hi₀⟩

end Submissions.PlyUpperTwoPowSqrt.CapCylinder
