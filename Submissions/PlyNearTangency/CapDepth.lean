import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Real Metric Set
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace Submissions.PlyNearTangency.CapDepth

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


/-- Volume of the `u`-cylinder at level `τ` inside the unit ball. -/
lemma cyl_vol_u (m : ℕ) (τ h β : ℝ) (hh : 0 ≤ h) (hβ : 0 ≤ β) (u : E (m+2)) (hu : ‖u‖ = 1) :
    volume {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (τ - h) τ ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2}
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
  have hpre : {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (τ - h) τ ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2}
      = Ψ ⁻¹' {v : E (m+2) | (v 0 ∈ Set.Icc (τ - h) τ) ∧
          ∑ j : Fin (m+1), (v j.succ)^2 ≤ β^2} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hkey w, ← hsplit (Ψ w), ← hnorm w]
  rw [hpre, (Ψ.measurePreserving).measure_preimage
      (meas_E m (τ - h) τ β).nullMeasurableSet,
    cyl_volume m (τ - h) τ β hβ]
  congr 2
  ring

lemma exists_unit {d : ℕ} (hd : 1 ≤ d) (p : E d) : ∃ u : E d, ‖u‖ = 1 ∧ p = ‖p‖ • u := by
  by_cases hp : p = 0
  · exact ⟨EuclideanSpace.single ⟨0, hd⟩ (1:ℝ), by simp, by simp [hp]⟩
  · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    refine ⟨‖p‖⁻¹ • p, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖p‖⁻¹)]
      field_simp
    · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

lemma cyl_subset (m : ℕ) {τ h β : ℝ} (hh : 0 ≤ h) (hτ : τ ≤ 0)
    (hβ2 : β^2 = 1 - (h - τ)^2)
    {p u : E (m+2)} (hu : ‖u‖ = 1) (hpu : p = ‖p‖ • u)
    (hcap : ‖p‖^2 + 2 * ‖p‖ * τ ≤ 2) :
    (fun w : E (m+2) => p + w) ''
        {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (τ - h) τ ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2}
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

lemma lens_vol_lower (m : ℕ) {τ h β : ℝ} (hh : 0 ≤ h) (hβ : 0 ≤ β) (hτ : τ ≤ 0)
    (hβ2 : β^2 = 1 - (h - τ)^2) (p : E (m+2)) (hcap : ‖p‖^2 + 2 * ‖p‖ * τ ≤ 2) :
    ENNReal.ofReal h * volume (closedBall (0 : E (m+1)) β)
      ≤ volume (closedBall p 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) := by
  obtain ⟨u, hu, hpu⟩ := exists_unit (d := m+2) (by omega) p
  set C : Set (E (m+2)) :=
    {w : E (m+2) | ⟪u, w⟫ ∈ Set.Icc (τ - h) τ ∧ ‖w‖^2 - ⟪u, w⟫^2 ≤ β^2} with hC
  have htr : volume ((fun w : E (m+2) => p + w) '' C) = volume C := by
    rw [Set.image_add_left]
    exact measure_preimage_add volume (-p) C
  calc ENNReal.ofReal h * volume (closedBall (0 : E (m+1)) β)
      = volume C := (cyl_vol_u m τ h β hh hβ u hu).symm
    _ = volume ((fun w : E (m+2) => p + w) '' C) := htr.symm
    _ ≤ volume (closedBall p 1 ∩ closedBall (0 : E (m+2)) (Real.sqrt 3)) :=
        measure_mono (cyl_subset m hh hτ hβ2 hu hpu hcap)

theorem packing_restricted (m : ℕ) {τ h β : ℝ} (hh : 0 ≤ h) (hβ : 0 ≤ β) (hτ : τ ≤ 0)
    (hβ2 : β^2 = 1 - (h - τ)^2) (N k : ℕ) (p : Fin N → E (m+2))
    (hthin : ∀ y : E (m+2), {j : Fin N | dist y (p j) ≤ 1}.ncard ≤ k)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, ‖p j‖^2 + 2 * ‖p j‖ * τ ≤ 2) :
    (T.card : ℝ) * (h * β^(m+1) * vb (m+1))
      ≤ (k : ℝ) * ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
  classical
  set W : Set (E (m+2)) := closedBall (0 : E (m+2)) (Real.sqrt 3) with hW_def
  have hlow : ∀ j ∈ T, ENNReal.ofReal (h * β^(m+1) * vb (m+1))
      ≤ volume (closedBall (p j) 1 ∩ W) := by
    intro j hj
    have := lens_vol_lower m hh hβ hτ hβ2 (p j) (hT j hj)
    refine le_trans (le_of_eq ?_) this
    rw [vol_ball_eq (m+1) β hβ, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ h * β^(m+1)),
      ENNReal.ofReal_mul hh, mul_assoc]
  have hsumT : (T.card : ℝ≥0∞) * ENNReal.ofReal (h * β^(m+1) * vb (m+1))
      ≤ ∑ j ∈ T, volume (closedBall (p j) 1 ∩ W) := by
    have := Finset.sum_le_sum hlow
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hext : ∑ j ∈ T, volume (closedBall (p j) 1 ∩ W)
      ≤ ∑ j : Fin N, volume (closedBall (p j) 1 ∩ W) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun _ _ _ => bot_le)
  have hsum2 := count_sum_le p W hthin
  have hWvol : volume W = ENNReal.ofReal ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
    rw [hW_def, vol_ball_eq (m+2) _ (Real.sqrt_nonneg 3),
      ENNReal.ofReal_mul (by positivity)]
  have hchain : (T.card : ℝ≥0∞) * ENNReal.ofReal (h * β^(m+1) * vb (m+1))
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
    calc (T.card : ℝ≥0∞) * ENNReal.ofReal (h * β^(m+1) * vb (m+1))
        ≤ ∑ j ∈ T, volume (closedBall (p j) 1 ∩ W) := hsumT
      _ ≤ ∑ j : Fin N, volume (closedBall (p j) 1 ∩ W) := hext
      _ ≤ (k : ℝ≥0∞) * volume W := hsum2
      _ = (k : ℝ≥0∞) * ENNReal.ofReal ((Real.sqrt 3)^(m+2) * vb (m+2)) := by rw [hWvol]
  rw [show ((T.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((T.card : ℝ)) by simp,
      show ((k : ℕ) : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) by simp,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hchain
  have hnn : (0:ℝ) ≤ (k : ℝ) * ((Real.sqrt 3)^(m+2) * vb (m+2)) := by
    have := (vb_pos (m+2)).le; positivity
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hchain

lemma tau_facts (η : ℝ) (h0 : 0 ≤ η) (h2 : η ≤ 1/2) :
    ∃ τ : ℝ, τ ≤ 0 ∧ -(1/2) ≤ τ ∧ (∀ s : ℝ, 0 ≤ s → s ≤ 2 - η → s^2 + 2*s*τ ≤ 2)
      ∧ (3/4) * (1 + η/2) ≤ 1 - τ^2 := by
  set S : ℝ := 2 - η with hS_def
  have hS1 : (3:ℝ)/2 ≤ S := by rw [hS_def]; linarith
  have hS2 : S ≤ 2 := by rw [hS_def]; linarith
  have hSpos : (0:ℝ) < S := by linarith
  refine ⟨(2 - S^2)/(2*S), ?_, ?_, ?_, ?_⟩
  · rw [div_nonpos_iff]; right; constructor <;> nlinarith
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · intro s hs0 hsS
    have hfac : s^2 + 2*s*((2 - S^2)/(2*S)) - 2 = (s - S) * (s + 2/S) := by
      field_simp; ring
    have h1 : s - S ≤ 0 := by linarith
    have h2' : (0:ℝ) ≤ s + 2/S := by positivity
    nlinarith [hfac]
  · have hpos2 : (0:ℝ) ≤ 2*S^3 + S^2 - 2*S - 4 := by
      nlinarith [hS1, hSpos, sq_nonneg (S - 3/2),
        mul_nonneg (sub_nonneg.mpr hS1) (sq_nonneg (S - 3/2))]
    have hkey : (0:ℝ) ≤ (2 - S) * (2*S^3 + S^2 - 2*S - 4) :=
      mul_nonneg (by linarith) hpos2
    have hexp : 1 - ((2 - S^2)/(2*S))^2 - (3/4) * (1 + (2 - S)/2)
        = ((2 - S) * (2*S^3 + S^2 - 2*S - 4)) / (8*S^2) := by
      field_simp; ring
    have hval : (0:ℝ) ≤ 1 - ((2 - S^2)/(2*S))^2 - (3/4) * (1 + (2 - S)/2) := by
      rw [hexp]; positivity
    have hη : η = 2 - S := by rw [hS_def]; ring
    rw [hη]
    linarith

set_option maxHeartbeats 1600000 in
lemma arith_key3 (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη2 : η ≤ 1/2) :
    ∃ τ h β : ℝ, τ ≤ 0 ∧ 0 < h ∧ 0 < β ∧ β^2 = 1 - (h - τ)^2 ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 2 - η → s^2 + 2*s*τ ≤ 2) ∧
      (Real.sqrt 3)^(m+2) * Real.sqrt ((1 + η/2)^(m+1))
        ≤ (100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) *
          (h * β^(m+1) * Real.sqrt (((m:ℝ)+2)/(2*π))) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  obtain ⟨τ, hτ0, hτhalf, hcap, hτsq⟩ := tau_facts η hη0 hη2
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
  have hG0 : (0:ℝ) < 1 + η/2 := by linarith
  -- β
  have hb2nn : (0:ℝ) ≤ 1 - (h - τ)^2 := by nlinarith
  set B2 : ℝ := 1 - (h - τ)^2 with hB2_def
  clear_value B2
  set β : ℝ := Real.sqrt B2 with hβ_def
  clear_value β
  have hβ : 0 ≤ β := by rw [hβ_def]; exact Real.sqrt_nonneg _
  have hβsq : β^2 = B2 := by rw [hβ_def]; exact Real.sq_sqrt (by rw [hB2_def] at hb2nn ⊢; linarith)
  have hB2low : (3/4) * (1 + η/2) * (1 - z) ≤ B2 := by
    have e1 : B2 = (1 - τ^2) + 2*h*τ - h^2 := by rw [hB2_def]; ring
    have e2 : (3/4) * (1 + η/2) * z ≥ h + h^2 := by
      rw [hz_def]; nlinarith
    nlinarith [hτsq, hh.le, hτ0]
  have hB2pos : 0 < B2 := by nlinarith
  have hβpos : 0 < β := by
    rcases lt_or_eq_of_le hβ with hlt | heq
    · exact hlt
    · exfalso; rw [← heq] at hβsq; simp at hβsq; linarith [hB2pos, hβsq.symm]
  refine ⟨τ, h, β, hτ0, hh, hβpos, by rw [hβsq, hB2_def], hcap, ?_⟩
  -- exponential lower bound
  have hexpz : Real.exp (-(2*z)) ≤ 1 - z := by
    have he : (1:ℝ) + 2*z ≤ Real.exp (2*z) := by
      have := Real.add_one_le_exp (2*z); linarith
    have hpos : (0:ℝ) < 1 + 2*z := by linarith
    have hb : Real.exp (-(2*z)) ≤ (1+2*z)⁻¹ := by
      rw [Real.exp_neg]; exact inv_anti₀ hpos he
    have hc : (1+2*z)⁻¹ ≤ 1 - z := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]; nlinarith
    linarith
  have hzm : 2*z*(M+1) ≤ 5 := by
    have h1 : h * (M+1) ≤ 1 := by
      rw [hh_def, div_mul_eq_mul_div, div_le_one hden]; linarith
    have h2 : h^2 * (M+1) ≤ 1/10 := by nlinarith
    rw [hz_def]; nlinarith
  have hzm' : Real.exp (-5) ≤ (1 - z)^(m+1) := by
    have hstep1 : Real.exp (-(2*z)) ^ (m+1) ≤ (1 - z)^(m+1) :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hexpz (m+1)
    have hstep2 : Real.exp (-(2*z)) ^ (m+1) = Real.exp (((m:ℝ)+1) * (-(2*z))) := by
      rw [show ((m:ℝ)+1) = ((m+1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul]
    have hstep3 : Real.exp (-5) ≤ Real.exp (((m:ℝ)+1) * (-(2*z))) := by
      apply Real.exp_le_exp.mpr
      have he : ((m:ℝ)+1) * (-(2*z)) = -(2*z*(M+1)) := by rw [hM]; ring
      rw [he]; linarith [hzm]
    rw [hstep2] at hstep1
    exact le_trans hstep3 hstep1
  have hB2m : ((3/4:ℝ) * (1 + η/2))^(m+1) * Real.exp (-5) ≤ B2^(m+1) := by
    have hnn0 : (0:ℝ) ≤ (3/4) * (1 + η/2) * (1 - z) := by
      have : (0:ℝ) ≤ 1 - z := by linarith
      positivity
    have h1 : ((3/4:ℝ) * (1 + η/2) * (1 - z))^(m+1) ≤ B2^(m+1) :=
      pow_le_pow_left₀ hnn0 hB2low (m+1)
    have h2 : ((3/4:ℝ) * (1 + η/2) * (1 - z))^(m+1)
        = ((3/4:ℝ) * (1 + η/2))^(m+1) * (1-z)^(m+1) := by rw [mul_pow]
    have h3 : ((3/4:ℝ) * (1 + η/2))^(m+1) * Real.exp (-5)
        ≤ ((3/4:ℝ) * (1 + η/2))^(m+1) * (1-z)^(m+1) :=
      mul_le_mul_of_nonneg_left hzm' (by positivity)
    rw [h2] at h1; linarith
  have hMh : (1:ℝ)/5 ≤ (M+2)*h := by
    rw [hh_def, mul_one_div, le_div_iff₀ hden]; linarith
  have hMh2 : (1:ℝ)/25 ≤ ((M+2)*h)^2 := by
    have h5 : ((1:ℝ)/5)^2 ≤ ((M+2)*h)^2 := pow_le_pow_left₀ (by norm_num) hMh 2
    have h6 : ((1:ℝ)/5)^2 = 1/25 := by norm_num
    linarith [h5, h6.le, h6.ge]
  -- squares
  have hM2 : (0:ℝ) < M + 2 := by linarith
  set G : ℝ := Real.sqrt ((1 + η/2)^(m+1)) with hG_def
  clear_value G
  have hGnn : 0 ≤ G := by rw [hG_def]; exact Real.sqrt_nonneg _
  have hGsq : G^2 = (1 + η/2)^(m+1) := by rw [hG_def]; exact Real.sq_sqrt (by positivity)
  set X : ℝ := (Real.sqrt 3)^(m+2) * G with hX_def
  set Y : ℝ := (100 * Real.exp 5) * 2^(m+2) * Real.sqrt (M+2) *
      (h * β^(m+1) * Real.sqrt ((M+2)/(2*π))) with hY_def
  have hYnn : 0 ≤ Y := by
    rw [hY_def]
    have h1 := Real.exp_pos (5:ℝ)
    have h2 : (0:ℝ) ≤ Real.sqrt (M+2) := Real.sqrt_nonneg _
    have h3 : (0:ℝ) ≤ Real.sqrt ((M+2)/(2*π)) := Real.sqrt_nonneg _
    positivity
  have hXnn : 0 ≤ X := by rw [hX_def]; positivity
  have hsq1 : (Real.sqrt (M+2))^2 = M+2 := Real.sq_sqrt hM2.le
  have hsq2 : (Real.sqrt ((M+2)/(2*π)))^2 = (M+2)/(2*π) := Real.sq_sqrt (by positivity)
  have hb2m : (β^(m+1))^2 = B2^(m+1) := by rw [← pow_mul, mul_comm, pow_mul, hβsq]
  have h2m : ((2:ℝ)^(m+2))^2 = 4^(m+2) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hY2 : Y^2 = (100 * Real.exp 5)^2 * ((M+2)*h)^2 * (4^(m+2) * B2^(m+1)) / (2*π) := by
    rw [hY_def, show ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt (M+2) *
        (h * β^(m+1) * Real.sqrt ((M+2)/(2*π))))^2
        = (100 * Real.exp 5)^2 * (h^2 * (Real.sqrt (M+2))^2 * (Real.sqrt ((M+2)/(2*π)))^2)
          * (((2:ℝ)^(m+2))^2 * (β^(m+1))^2) by ring, hsq1, hsq2, hb2m, h2m]
    field_simp
  have hX2 : X^2 = (3:ℝ)^(m+2) * (1 + η/2)^(m+1) := by
    rw [hX_def, mul_pow, hGsq, ← pow_mul, mul_comm (m+2) 2, pow_mul,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hexp1 : (1:ℝ) ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
  have hlow : (100 * Real.exp 5)^2 * (1/25) *
      (4^(m+2) * (((3/4:ℝ) * (1 + η/2))^(m+1) * Real.exp (-5))) / (2*π) ≤ Y^2 := by
    rw [hY2]
    have h4 : (0:ℝ) < (4:ℝ)^(m+2) := by positivity
    gcongr
  have h44 : (4:ℝ)^(m+2) * (3/4:ℝ)^(m+1) = 4 * 3^(m+1) := by
    rw [pow_succ, mul_comm ((4:ℝ)^(m+1)) 4, mul_assoc, ← mul_pow]
    norm_num
  have h43 : (4:ℝ)^(m+2) * ((3/4:ℝ) * (1 + η/2))^(m+1)
      = 4 * (3^(m+1) * (1 + η/2)^(m+1)) := by
    rw [mul_pow, ← mul_assoc, h44]; ring
  have hE : (Real.exp 5)^2 * Real.exp (-5) = Real.exp 5 := by
    rw [Real.exp_neg, sq]; field_simp
  have hsimp : (100 * Real.exp 5)^2 * (1/25) *
      ((4:ℝ)^(m+2) * (((3/4:ℝ) * (1 + η/2))^(m+1) * Real.exp (-5))) / (2*π)
      = (1600 * Real.exp 5 / (2*π)) * (3^(m+1) * (1 + η/2)^(m+1)) := by
    calc (100 * Real.exp 5)^2 * (1/25) *
          ((4:ℝ)^(m+2) * (((3/4:ℝ) * (1 + η/2))^(m+1) * Real.exp (-5))) / (2*π)
        = (400 * ((Real.exp 5)^2 * Real.exp (-5)) *
            ((4:ℝ)^(m+2) * ((3/4:ℝ) * (1 + η/2))^(m+1))) / (2*π) := by ring
      _ = (400 * Real.exp 5 * (4 * (3^(m+1) * (1 + η/2)^(m+1)))) / (2*π) := by rw [hE, h43]
      _ = (1600 * Real.exp 5 / (2*π)) * (3^(m+1) * (1 + η/2)^(m+1)) := by ring
  have h3m : (0:ℝ) < 3^(m+1) * (1 + η/2)^(m+1) := by positivity
  have hgoal : (3:ℝ)^(m+2) * (1 + η/2)^(m+1)
      ≤ (1600 * Real.exp 5 / (2*π)) * (3^(m+1) * (1 + η/2)^(m+1)) := by
    have hpib : π ≤ 4 := Real.pi_le_four
    have h1 : (3:ℝ) ≤ 1600 * Real.exp 5 / (2*π) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    calc (3:ℝ)^(m+2) * (1 + η/2)^(m+1)
        = (3^(m+1) * (1 + η/2)^(m+1)) * 3 := by rw [pow_succ]; ring
      _ ≤ (3^(m+1) * (1 + η/2)^(m+1)) * (1600 * Real.exp 5 / (2*π)) :=
          mul_le_mul_of_nonneg_left h1 h3m.le
      _ = (1600 * Real.exp 5 / (2*π)) * (3^(m+1) * (1 + η/2)^(m+1)) := by ring
  have hfinal : X^2 ≤ Y^2 := by
    rw [hX2]
    calc (3:ℝ)^(m+2) * (1 + η/2)^(m+1)
        ≤ (1600 * Real.exp 5 / (2*π)) * (3^(m+1) * (1 + η/2)^(m+1)) := hgoal
      _ = (100 * Real.exp 5)^2 * (1/25) *
          ((4:ℝ)^(m+2) * (((3/4:ℝ) * (1 + η/2))^(m+1) * Real.exp (-5))) / (2*π) := hsimp.symm
      _ ≤ Y^2 := hlow
  have := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq hXnn, Real.sqrt_sq hYnn] at this

set_option maxHeartbeats 1600000 in
/-- The submitted proof of `Statements.PlyNearTangency.statement`. -/
theorem proof :
    ∃ K : ℝ,
      ∀ (d : ℕ), 2 ≤ d → ∀ (η : ℝ), 0 ≤ η → η ≤ 1/2 →
        ∀ (N k : ℕ) (p : Fin N → EuclideanSpace ℝ (Fin d)),
          (∀ y : EuclideanSpace ℝ (Fin d), {j : Fin N | dist y (p j) ≤ 1}.ncard ≤ k) →
          ({j : Fin N | ‖p j‖ ≤ 2 - η}.ncard : ℝ) * Real.sqrt ((1 + η/2)^(d-1))
            ≤ K * 2 ^ d * Real.sqrt d * k := by
  classical
  refine ⟨100 * Real.exp 5, ?_⟩
  intro d hd η hη0 hη2 N k p hthin
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  obtain ⟨τ, h, β, hτ0, hh, hβ, hβ2, hcap, hineq⟩ := arith_key3 m η hη0 hη2
  have hpi : (0:ℝ) < π := Real.pi_pos
  set S : ℝ := Real.sqrt (((m:ℝ)+2)/(2*π)) with hS_def
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  set P : ℝ := h * β^(m+1) with hP_def
  have hP : 0 < P := by rw [hP_def]; positivity
  set T : Finset (Fin N) := {j : Fin N | ‖p j‖ ≤ 2 - η}.toFinset with hT_def
  have hTcard : ({j : Fin N | ‖p j‖ ≤ 2 - η}.ncard : ℝ) = (T.card : ℝ) := by
    rw [hT_def, ← Set.ncard_eq_toFinset_card']
  have hTs : ∀ j ∈ T, ‖p j‖^2 + 2 * ‖p j‖ * τ ≤ 2 := by
    intro j hj
    rw [hT_def, Set.mem_toFinset] at hj
    exact hcap _ (norm_nonneg _) hj
  have hpack := packing_restricted m hh.le hβ.le hτ0 hβ2 N k p hthin T hTs
  have hr := vb_ratio m
  have hV2 : 0 < vb (m+2) := vb_pos (m+2)
  have hT0 : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hstep : (T.card : ℝ) * (P * S) * vb (m+2)
      ≤ (k:ℝ) * (Real.sqrt 3)^(m+2) * vb (m+2) := by
    have hSV : S * vb (m+2) ≤ vb (m+1) := by rw [hS_def]; exact hr
    have h1 : (T.card : ℝ) * (P * (S * vb (m+2))) ≤ (T.card : ℝ) * (P * vb (m+1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSV hP.le) hT0
    calc (T.card : ℝ) * (P * S) * vb (m+2) = (T.card : ℝ) * (P * (S * vb (m+2))) := by ring
      _ ≤ (T.card : ℝ) * (P * vb (m+1)) := h1
      _ = (T.card : ℝ) * (h * β^(m+1) * vb (m+1)) := by rw [hP_def]
      _ ≤ (k:ℝ) * ((Real.sqrt 3)^(m+2) * vb (m+2)) := hpack
      _ = (k:ℝ) * (Real.sqrt 3)^(m+2) * vb (m+2) := by ring
  have hcancel : (T.card : ℝ) * (P * S) ≤ (k:ℝ) * (Real.sqrt 3)^(m+2) :=
    le_of_mul_le_mul_right hstep hV2
  set G : ℝ := Real.sqrt ((1 + η/2)^(m+1)) with hG_def
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hup : (k:ℝ) * ((Real.sqrt 3)^(m+2) * G)
      ≤ ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k) * (P * S) := by
    calc (k:ℝ) * ((Real.sqrt 3)^(m+2) * G)
        ≤ (k:ℝ) * ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) *
            (h * β^(m+1) * Real.sqrt (((m:ℝ)+2)/(2*π)))) :=
          mul_le_mul_of_nonneg_left (by rw [hG_def]; exact hineq) hk0
      _ = ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k) * (P * S) := by
          rw [hP_def, hS_def]; ring
  have hfin : ((T.card : ℝ) * G) * (P * S)
      ≤ ((100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k) * (P * S) := by
    have h1 : ((T.card : ℝ) * G) * (P * S) = ((T.card : ℝ) * (P * S)) * G := by ring
    have h2 : ((T.card : ℝ) * (P * S)) * G ≤ ((k:ℝ) * (Real.sqrt 3)^(m+2)) * G :=
      mul_le_mul_of_nonneg_right hcancel hG
    have h3 : ((k:ℝ) * (Real.sqrt 3)^(m+2)) * G = (k:ℝ) * ((Real.sqrt 3)^(m+2) * G) := by ring
    rw [h1]
    linarith [h2, hup, h3.le, h3.ge]
  have hres : (T.card : ℝ) * G
      ≤ (100 * Real.exp 5) * 2^(m+2) * Real.sqrt ((m:ℝ)+2) * k :=
    le_of_mul_le_mul_right hfin (by positivity)
  have hc : (((m+2:ℕ)):ℝ) = (m:ℝ) + 2 := by push_cast; ring
  rw [hTcard, show (m+2) - 1 = m+1 by omega, ← hG_def, hc]
  exact hres

end Submissions.PlyNearTangency.CapDepth
