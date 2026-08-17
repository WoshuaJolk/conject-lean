import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Real Metric Set
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace Submissions.PlyGaussianDual.Poser

variable {d : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def g (lam : ℝ) (y : E d) : ℝ := rexp (-lam * ‖y‖ ^ 2)

lemma g_pos (lam : ℝ) (y : E d) : 0 < g lam y := Real.exp_pos _


lemma integrable_g (lam : ℝ) (hlam : 0 < lam) : Integrable (g (d := d) lam) := by
  have hb : (0:ℝ) < ((lam : ℂ)).re := by simpa using hlam
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E d) hb 0 0
  refine (h.re).congr ?_
  filter_upwards with v
  simp only [inner_zero_left, zero_mul, add_zero, g]
  rw [show (-(lam : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2) = (((-lam * ‖v‖ ^ 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  first
  | simp only [Complex.ofReal_re]
  | simp only [RCLike.ofReal_re]
  | exact Complex.ofReal_re _
  | exact RCLike.ofReal_re _

lemma integral_g (lam : ℝ) (hlam : 0 < lam) :
    ∫ y : E d, g lam y = (π / lam) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E d) hlam
  rw [finrank_euclideanSpace_fin] at h
  exact h

lemma symm_bound (c : ℝ) (p : E d) :
    (volume (closedBall (0 : E d) 1)).toReal
      ≤ ∫ u in closedBall (0 : E d) 1, rexp (-c * ⟪p, u⟫) := by
  set B : Set (E d) := closedBall 0 1 with hBdef
  have hBneg : Neg.neg ⁻¹' B = B := by ext u; simp [hBdef]
  have hcont : Continuous fun u : E d => rexp (-c * ⟪p, u⟫) := by fun_prop
  have hcont' : Continuous fun u : E d => rexp (c * ⟪p, u⟫) := by fun_prop
  have hint : IntegrableOn (fun u : E d => rexp (-c * ⟪p, u⟫)) B :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hint' : IntegrableOn (fun u : E d => rexp (c * ⟪p, u⟫)) B :=
    hcont'.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hflip : ∫ u in B, rexp (c * ⟪p, u⟫) = ∫ u in B, rexp (-c * ⟪p, u⟫) := by
    have h := (Measure.measurePreserving_neg (volume : Measure (E d))).setIntegral_preimage_emb
      measurableEmbedding_neg (fun y : E d => rexp (-c * ⟪p, y⟫)) B
    rw [hBneg] at h
    simpa [inner_neg_right, neg_mul, mul_neg] using h
  have hpt : ∀ u ∈ B, (2 : ℝ) ≤ rexp (-c * ⟪p, u⟫) + rexp (c * ⟪p, u⟫) := by
    intro u _
    have h2 : 0 < rexp (-c * ⟪p, u⟫) := Real.exp_pos _
    have h3 : 0 < rexp (c * ⟪p, u⟫) := Real.exp_pos _
    have h1 : rexp (-c * ⟪p, u⟫) * rexp (c * ⟪p, u⟫) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    nlinarith [sq_nonneg (rexp (-c * ⟪p, u⟫) - rexp (c * ⟪p, u⟫))]
  have hmono : ∫ _u in B, (2 : ℝ) ≤ ∫ u in B, (rexp (-c * ⟪p, u⟫) + rexp (c * ⟪p, u⟫)) :=
    setIntegral_mono_on (integrableOn_const measure_closedBall_lt_top.ne) (hint.add hint') measurableSet_closedBall hpt
  rw [integral_add hint hint', hflip, setIntegral_const, measureReal_def, smul_eq_mul] at hmono
  linarith

lemma ball_lower (lam : ℝ) (hlam : 0 < lam) (p : E d) (hp : ‖p‖ ≤ 2) :
    rexp (-5 * lam) * (volume (closedBall (0 : E d) 1)).toReal
      ≤ ∫ y in closedBall p 1, g lam y := by
  have hpre : (fun u : E d => p + u) ⁻¹' (closedBall p 1) = closedBall (0 : E d) 1 := by
    ext u; simp [mem_closedBall_iff_norm, dist_eq_norm]
  have htr : ∫ u in closedBall (0 : E d) 1, g lam (p + u) = ∫ y in closedBall p 1, g lam y := by
    have h := (measurePreserving_add_left (volume : Measure (E d)) p).setIntegral_preimage_emb
      (measurableEmbedding_addLeft p) (fun y : E d => g lam y) (closedBall p 1)
    rw [hpre] at h; exact h
  rw [← htr]
  have hcontL : Continuous fun u : E d => rexp (-5*lam) * rexp (-(2*lam) * ⟪p, u⟫) := by fun_prop
  have hcontR : Continuous fun u : E d => g lam (p + u) := by
    unfold g; fun_prop
  have hIL : IntegrableOn (fun u : E d => rexp (-5*lam) * rexp (-(2*lam) * ⟪p, u⟫))
      (closedBall (0 : E d) 1) := hcontL.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hIR : IntegrableOn (fun u : E d => g lam (p + u)) (closedBall (0 : E d) 1) :=
    hcontR.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hpt : ∀ u ∈ closedBall (0 : E d) 1,
      rexp (-5*lam) * rexp (-(2*lam) * ⟪p, u⟫) ≤ g lam (p + u) := by
    intro u hu
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    have hn : ‖p + u‖^2 ≤ 5 + 2 * ⟪p, u⟫ := by
      rw [norm_add_sq_real]; nlinarith [norm_nonneg p, norm_nonneg u]
    have hstep : -5*lam + (-(2*lam)) * ⟪p, u⟫ ≤ -lam * ‖p+u‖^2 := by nlinarith
    calc rexp (-5*lam) * rexp (-(2*lam) * ⟪p, u⟫)
        = rexp (-5*lam + (-(2*lam)) * ⟪p, u⟫) := (Real.exp_add _ _).symm
      _ ≤ rexp (-lam * ‖p+u‖^2) := Real.exp_le_exp.2 hstep
      _ = g lam (p + u) := rfl
  have hmono := setIntegral_mono_on hIL hIR measurableSet_closedBall hpt
  refine le_trans ?_ hmono
  rw [integral_const_mul]
  have := symm_bound (d := d) (2*lam) p
  nlinarith [Real.exp_pos (-5*lam), ENNReal.toReal_nonneg (a := volume (closedBall (0:E d) 1))]

theorem count_le (lam : ℝ) (hlam : 0 < lam) (N k : ℕ) (p : Fin N → E d)
    (hp : ∀ i, ‖p i‖ ≤ 2)
    (hthin : ∀ y : E d, ({i : Fin N | dist y (p i) ≤ 1}).ncard ≤ k) :
    (N : ℝ) * (rexp (-5 * lam) * (volume (closedBall (0 : E d) 1)).toReal)
      ≤ k * (π / lam) ^ ((d : ℝ) / 2) := by
  have hgi := integrable_g (d := d) lam hlam
  have hind : ∀ i : Fin N, Integrable ((closedBall (p i) 1).indicator (g (d := d) lam)) :=
    fun i => hgi.indicator measurableSet_closedBall
  have hpt : ∀ y : E d, ∑ i : Fin N, (closedBall (p i) 1).indicator (g lam) y ≤ k * g lam y := by
    intro y
    classical
    have hset : {i : Fin N | dist y (p i) ≤ 1}.toFinset
        = Finset.univ.filter (fun i => dist y (p i) ≤ 1) := by ext i; simp
    have hcard : (Finset.univ.filter (fun i : Fin N => dist y (p i) ≤ 1)).card ≤ k := by
      rw [← hset, ← Set.ncard_eq_toFinset_card']; exact hthin y
    have hrw : ∑ i : Fin N, (closedBall (p i) 1).indicator (g lam) y
        = ((Finset.univ.filter (fun i : Fin N => dist y (p i) ≤ 1)).card : ℝ) * g lam y := by
      simp only [Set.indicator_apply, Metric.mem_closedBall]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (g_pos lam y).le
  have hstep1 : ∑ i : Fin N, ∫ y in closedBall (p i) 1, g lam y ≤ k * ∫ y : E d, g lam y := by
    have h1 : ∫ y : E d, ∑ i : Fin N, (closedBall (p i) 1).indicator (g lam) y
        = ∑ i : Fin N, ∫ y in closedBall (p i) 1, g lam y := by
      rw [integral_finsetSum _ (fun i _ => hind i)]
      exact Finset.sum_congr rfl (fun i _ => integral_indicator measurableSet_closedBall)
    rw [← h1, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ (fun i _ => hind i)) (hgi.const_mul _)
      (fun y => hpt y)
  have hstep2 : (N : ℝ) * (rexp (-5 * lam) * (volume (closedBall (0 : E d) 1)).toReal)
      ≤ ∑ i : Fin N, ∫ y in closedBall (p i) 1, g lam y := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ball_lower lam hlam (p i) (hp i))
    simpa [Finset.sum_const, mul_comm] using this
  calc (N : ℝ) * (rexp (-5 * lam) * (volume (closedBall (0 : E d) 1)).toReal)
      ≤ ∑ i : Fin N, ∫ y in closedBall (p i) 1, g lam y := hstep2
    _ ≤ k * ∫ y : E d, g lam y := hstep1
    _ = k * (π / lam) ^ ((d : ℝ) / 2) := by rw [integral_g lam hlam]

/-- The submitted proof of `Statements.PlyGaussianDual.statement`. -/
theorem proof :
    ∀ (d : ℕ) (lam : ℝ), 0 < lam →
      ∀ (N k : ℕ) (p : Fin N → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖p i‖ ≤ 2) →
        (∀ y : EuclideanSpace ℝ (Fin d), {i : Fin N | dist y (p i) ≤ 1}.ncard ≤ k) →
        (N : ℝ) * (Real.exp (-5 * lam) *
            (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
          ≤ k * (Real.pi / lam) ^ ((d : ℝ) / 2) :=
  fun d lam hlam N k p hp hthin => count_le lam hlam N k p hp hthin

end Submissions.PlyGaussianDual.Poser
