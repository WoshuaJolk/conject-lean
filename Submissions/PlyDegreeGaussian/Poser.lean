import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Real Metric Set
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace Submissions.PlyDegreeGaussian.Poser


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


/-- The submitted proof of `Statements.PlyDegreeGaussian.statement`. -/
theorem proof :
    ∀ (d : ℕ) (lam : ℝ), 0 < lam → ∀ (n k : ℕ), 0 < n →
      ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ), (∀ i, 0 < r i) →
        (∀ p : EuclideanSpace ℝ (Fin d),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀ : Fin n,
          ({i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩
                Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard : ℝ)
            * (Real.exp (-5 * lam) *
                (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
          ≤ k * (Real.pi / lam) ^ ((d : ℝ) / 2) := by
  intro d lam hlam n k hn x r hr hthin
  have hvpos : 0 < (volume (Metric.closedBall (0 : E d) 1)).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt ?_) (ne_of_lt measure_closedBall_lt_top)
    exact measure_closedBall_pos volume 0 one_pos
  set B : ℝ := Real.exp (-5 * lam) * (volume (Metric.closedBall (0 : E d) 1)).toReal with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hM : ∀ (N : ℕ) (q : Fin N → E d), (∀ j, ‖q j‖ ≤ 2) →
      (∀ y : E d, {j : Fin N | dist y (q j) ≤ 1}.ncard ≤ k) →
      (N : ℝ) ≤ (k * (Real.pi / lam) ^ ((d : ℝ) / 2)) / B := by
    intro N q h1 h2
    rw [le_div_iff₀ hBpos]
    exact count_le lam hlam N k q h1 h2
  obtain ⟨i₀, hi₀⟩ := degree_le hn x r hr hthin _ hM
  exact ⟨i₀, by rw [← le_div_iff₀ hBpos]; exact hi₀⟩

end Submissions.PlyDegreeGaussian.Poser
