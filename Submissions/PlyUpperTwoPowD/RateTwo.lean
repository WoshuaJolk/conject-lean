import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin

open MeasureTheory Metric Set
open scoped ENNReal

namespace Submissions.PlyUpperTwoPowD.RateTwo

noncomputable def diagMap (n : ℕ) (w : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun u := WithLp.toLp 2 (fun i => w i * u.ofLp i)
  map_add' u v := by ext i; simp [mul_add]
  map_smul' c u := by ext i; simp; ring

lemma diagMap_apply (n : ℕ) (w : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (diagMap n w u).ofLp i = w i * u.ofLp i := rfl

lemma diagMap_det (n : ℕ) (w : Fin n → ℝ) :
    LinearMap.det (diagMap n w) = ∏ i, w i := by
  have hb : diagMap n w = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (Matrix.diagonal w) := by
    apply Module.Basis.ext (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    intro j
    rw [Matrix.toLin_self]
    ext i
    simp [diagMap_apply, Matrix.diagonal, Finset.sum_ite_eq']
    split_ifs with h <;> simp [h]
  rw [hb, LinearMap.det_toLin, Matrix.det_diagonal]

lemma norm_sq_eq (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ‖u‖^2 = ∑ i, (u.ofLp i)^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  simp [sq_abs]

/-- The spherical cap of height `1/2` at the bottom of the unit ball, in a fixed frame. -/
def cap (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n+1))) :=
  {u | ‖u‖ ≤ 1 ∧ u.ofLp 0 ≤ -(1/2)}

lemma cap_lower (n : ℕ) (α β c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hc : 1/2 ≤ c - α)
    (hmain : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → (c - α*t)^2 + β^2*(1-t^2) ≤ 1) :
    ENNReal.ofReal (α * β^n) * volume (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1)
      ≤ volume (cap n) := by
  classical
  set w : Fin (n+1) → ℝ := fun i => if i = 0 then α else β with hw
  set L := diagMap (n+1) w with hL
  set v0 : EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 (fun i => if i = 0 then -c else 0) with hv0
  have hdet : LinearMap.det L = α * β^n := by
    rw [hL, diagMap_det, hw, Fin.prod_univ_succ]
    simp
  have hsub : (fun y => v0 + y) '' (L '' (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1)) ⊆ cap n := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    have hy2 : ‖y‖^2 ≤ 1 := by nlinarith [norm_nonneg y]
    have hcoord : ∀ i : Fin (n+1), (v0 + L y).ofLp i = (if i = 0 then -c else 0) + w i * y.ofLp i := by
      intro i; simp [hv0, hL, diagMap_apply]
    have h0 : (v0 + L y).ofLp 0 = -c + α * y.ofLp 0 := by
      rw [hcoord]; simp [hw]
    have hsucc : ∀ i : Fin n, (v0 + L y).ofLp i.succ = β * y.ofLp i.succ := by
      intro i; rw [hcoord]; simp [hw, Fin.succ_ne_zero]
    have hsplit : ‖y‖^2 = (y.ofLp 0)^2 + ∑ i : Fin n, (y.ofLp i.succ)^2 := by
      rw [norm_sq_eq, Fin.sum_univ_succ]
    have ht1 : (y.ofLp 0)^2 ≤ 1 := by nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (y.ofLp (Fin.succ i)))]
    have htlo : -1 ≤ y.ofLp 0 := by nlinarith
    have hthi : y.ofLp 0 ≤ 1 := by nlinarith
    constructor
    · have : ‖v0 + L y‖^2 = (c - α * y.ofLp 0)^2 + β^2 * (‖y‖^2 - (y.ofLp 0)^2) := by
        rw [norm_sq_eq, Fin.sum_univ_succ, h0, hsplit]
        have : ∑ i : Fin n, ((v0 + L y).ofLp i.succ)^2 = ∑ i : Fin n, (β * y.ofLp i.succ)^2 := by
          exact Finset.sum_congr rfl (fun i _ => by rw [hsucc])
        rw [this]
        simp only [mul_pow]
        rw [← Finset.mul_sum]
        ring
      have hle : ‖v0 + L y‖^2 ≤ 1 := by
        rw [this]
        have := hmain (y.ofLp 0) htlo hthi
        nlinarith [sq_nonneg β]
      nlinarith [norm_nonneg (v0 + L y)]
    · rw [h0]; nlinarith
  calc ENNReal.ofReal (α * β^n) * volume (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1)
      = volume (L '' (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1)) := by
        rw [Measure.addHaar_image_linearMap, hdet, abs_of_pos (by positivity)]
    _ = volume ((fun y => v0 + y) '' (L '' (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1))) := by
        rw [Set.image_add_left]
        exact (measure_preimage_add volume (-v0) _).symm
    _ ≤ volume (cap n) := measure_mono hsub


lemma cap_meas (n : ℕ) : MeasurableSet (cap n) := by
  have h1 : {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext u; simp [Metric.mem_closedBall, dist_zero_right]
  have h2 : MeasurableSet {u : EuclideanSpace ℝ (Fin (n+1)) | u.ofLp 0 ≤ -(1/2)} := by
    have : Continuous (fun u : EuclideanSpace ℝ (Fin (n+1)) => u.ofLp 0) :=
      (EuclideanSpace.proj (0 : Fin (n+1))).continuous
    exact (isClosed_le this continuous_const).measurableSet
  have : cap n = {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ 1} ∩ {u | u.ofLp 0 ≤ -(1/2)} := rfl
  rw [this, h1]
  exact (measurableSet_closedBall).inter h2

lemma cap_rot (n : ℕ) (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖ = 1) :
    volume {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ 1 ∧ inner ℝ e u ≤ -(1/2)}
      = volume (cap n) := by
  classical
  have horth : Orthonormal ℝ (({0} : Set (Fin (n+1))).domRestrict (fun _ : Fin (n+1) => e)) := by
    constructor
    · intro i; simpa [Set.domRestrict] using he
    · intro i j hij
      exact absurd (Subtype.ext (by rw [i.2, j.2] : (i : Fin (n+1)) = j)) hij
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
      (by simp)
  have hb0 : b 0 = e := hb 0 rfl
  have key : {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ 1 ∧ inner ℝ e u ≤ -(1/2)}
      = (b.repr) ⁻¹' (cap n) := by
    ext u
    have h1 : ‖b.repr u‖ = ‖u‖ := b.repr.norm_map u
    have h2 : (b.repr u).ofLp 0 = inner ℝ e u := by
      have h := b.repr.inner_map_map (b 0) u
      rw [b.repr_self, EuclideanSpace.inner_single_left, hb0] at h
      simpa using h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, cap, h1, h2]
  rw [key]
  exact (b.measurePreserving_repr).measure_preimage (cap_meas n).nullMeasurableSet


/-- Counting bound: if the balls `closedBall (q i) 1` cover no point more than `k` times,
then the total mass they put on a set `S` is at most `k * volume S`. -/
lemma sum_meas_inter_le {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (S : Set X)
    (hS : MeasurableSet S) (k : ℕ) (hk : ∀ y, {i | y ∈ A i}.ncard ≤ k) :
    ∑ i, μ (A i ∩ S) ≤ (k : ℝ≥0∞) * μ S := by
  classical
  have step1 : ∀ i, μ (A i ∩ S) = ∫⁻ y in S, (A i).indicator (1 : X → ℝ≥0∞) y ∂μ := by
    intro i
    rw [lintegral_indicator_one (hA i), Measure.restrict_apply (hA i)]
  have step2 : ∑ i, μ (A i ∩ S)
      = ∫⁻ y in S, ∑ i, (A i).indicator (1 : X → ℝ≥0∞) y ∂μ := by
    rw [lintegral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => step1 i)
    · intro i _
      exact (measurable_const.indicator (hA i))
  have step3 : ∀ y, ∑ i, (A i).indicator (1 : X → ℝ≥0∞) y ≤ (k : ℝ≥0∞) := by
    intro y
    have : ∑ i, (A i).indicator (1 : X → ℝ≥0∞) y
        = ((Finset.univ.filter (fun i => y ∈ A i)).card : ℝ≥0∞) := by
      rw [← Finset.sum_boole]
      exact Finset.sum_congr rfl (fun i _ => by by_cases h : y ∈ A i <;> simp [h])
    rw [this]
    have hcard : (Finset.univ.filter (fun i => y ∈ A i)).card = {i | y ∈ A i}.ncard := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext i; simp
    rw [hcard]
    exact_mod_cast Nat.cast_le.mpr (hk y)
  rw [step2]
  calc ∫⁻ y in S, ∑ i, (A i).indicator (1 : X → ℝ≥0∞) y ∂μ
      ≤ ∫⁻ _ in S, (k : ℝ≥0∞) ∂μ := lintegral_mono (fun y => step3 y)
    _ = (k : ℝ≥0∞) * μ S := setLIntegral_const S _


lemma cap_at_le (n : ℕ) (q : EuclideanSpace ℝ (Fin (n+1))) (hq : ‖q‖ ≤ 2) :
    volume (cap n)
      ≤ volume (closedBall q 1 ∩ closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt 3)) := by
  classical
  set e : EuclideanSpace ℝ (Fin (n+1)) :=
    if q = 0 then EuclideanSpace.single 0 1 else ‖q‖⁻¹ • q with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def]; split_ifs with h
    · simp
    · rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)
  have hinner : ∀ u, inner ℝ q u = ‖q‖ * inner ℝ e u := by
    intro u
    rw [he_def]; split_ifs with h
    · simp [h]
    · rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_mul]
  set T := {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ 1 ∧ inner ℝ e u ≤ -(1/2)} with hT
  have h2 : volume ((fun u => q + u) '' T) = volume T := by
    rw [Set.image_add_left]; exact measure_preimage_add volume (-q) _
  calc volume (cap n) = volume T := (cap_rot n e he).symm
    _ = volume ((fun u => q + u) '' T) := h2.symm
    _ ≤ _ := by
        apply measure_mono
        rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
        have hs0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg q
        have hnorm : ‖q + u‖^2 ≤ 3 := by
          rw [norm_add_sq_real, hinner u]
          nlinarith [norm_nonneg u, sq_nonneg (‖q‖ - 2), sq_nonneg ‖u‖]
        constructor
        · simp only [Metric.mem_closedBall, dist_eq_norm]
          simpa using hu1
        · simp only [Metric.mem_closedBall, dist_zero_right]
          have := Real.sqrt_le_sqrt hnorm
          rw [Real.sqrt_sq (norm_nonneg _)] at this
          exact this

lemma packing_ennreal {ι : Type*} [Fintype ι] (n k : ℕ)
    (q : ι → EuclideanSpace ℝ (Fin (n+1))) (hq : ∀ i, ‖q i‖ ≤ 2)
    (hthin : ∀ y, {i | dist y (q i) ≤ 1}.ncard ≤ k) :
    (Fintype.card ι : ℝ≥0∞) * volume (cap n)
      ≤ (k : ℝ≥0∞) * volume (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt 3)) := by
  classical
  have hsum := sum_meas_inter_le volume (fun i => closedBall (q i) 1)
      (fun i => measurableSet_closedBall) (closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt 3))
      measurableSet_closedBall k (by
        intro y
        have : {i | y ∈ closedBall (q i) 1} = {i | dist y (q i) ≤ 1} := by
          ext i; simp [Metric.mem_closedBall]
        rw [this]; exact hthin y)
  calc (Fintype.card ι : ℝ≥0∞) * volume (cap n)
      = ∑ _i : ι, volume (cap n) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ i, volume (closedBall (q i) 1 ∩ closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt 3)) :=
        Finset.sum_le_sum (fun i _ => cap_at_le n (q i) (hq i))
    _ ≤ _ := hsum


/-- The explicit packing count: at most `16 * d * 2 ^ d * k` unit balls with centres in the
ball of radius `2` can be `k`-thin, where `d = n + 1`. -/
lemma card_le (n k : ℕ) {ι : Type*} [Fintype ι] (q : ι → EuclideanSpace ℝ (Fin (n+1)))
    (hq : ∀ i, ‖q i‖ ≤ 2) (hthin : ∀ y, {i | dist y (q i) ≤ 1}.ncard ≤ k) :
    Fintype.card ι ≤ 16 * (n+1) * 2^(n+1) * k := by
  classical
  set D : ℝ := (n : ℝ) + 1 with hD
  have hD1 : (1:ℝ) ≤ D := by rw [hD]; linarith [Nat.cast_nonneg (α := ℝ) n]
  set A : ℝ := 1/(8*D) with hA_def
  have hA : 0 < A := by rw [hA_def]; positivity
  have hA8 : A ≤ 1/8 := by
    rw [hA_def]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  set B2 : ℝ := 3/4 - 3*A with hB2_def
  have hB2 : 0 < B2 := by rw [hB2_def]; linarith
  set B : ℝ := Real.sqrt B2 with hB_def
  have hB : 0 < B := Real.sqrt_pos.mpr hB2
  have hBsq : B^2 = B2 := Real.sq_sqrt hB2.le
  -- the cap lower bound at these parameters
  have hcap : ENNReal.ofReal (A * B^n)
      * volume (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1) ≤ volume (cap n) := by
    refine cap_lower n A B (1/2 + A) hA hB (by linarith) ?_
    intro t ht1 ht2
    rw [hBsq, hB2_def]
    nlinarith [sq_nonneg t, mul_nonneg (by nlinarith : (0:ℝ) ≤ 3/4 - 3*A - A^2) (sq_nonneg t),
      mul_nonneg (by nlinarith : (0:ℝ) ≤ A + 2*A^2) (by linarith : (0:ℝ) ≤ t + 1)]
  -- the two ball volumes
  set V : ℝ≥0∞ := volume (ball (0:EuclideanSpace ℝ (Fin (n+1))) 1) with hV_def
  have hV0 : V ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hcb1 : volume (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) 1) = V := by
    rw [Measure.addHaar_closedBall volume 0 zero_le_one]; simp [hV_def]
  have hcb3 : volume (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt 3))
      = ENNReal.ofReal ((Real.sqrt 3)^(n+1)) * V := by
    rw [Measure.addHaar_closedBall volume 0 (Real.sqrt_nonneg 3)]
    simp [hV_def]
  -- the key real inequality
  have hkey : (Real.sqrt 3)^(n+1) ≤ (16 * ((n:ℝ)+1) * 2^(n+1)) * (A * B^n) := by
    have h16 : 16 * ((n:ℝ)+1) * A = 2 := by rw [hA_def, ← hD]; field_simp; ring
    have hrw : (16 * ((n:ℝ)+1) * 2^(n+1)) * (A * B^n) = 2 * 2^(n+1) * B^n := by
      rw [show (16 * ((n:ℝ)+1) * 2^(n+1)) * (A * B^n)
            = (16 * ((n:ℝ)+1) * A) * (2^(n+1) * B^n) by ring, h16]; ring
    rw [hrw]
    have hL0 : (0:ℝ) ≤ (Real.sqrt 3)^(n+1) := by positivity
    have hR0 : (0:ℝ) ≤ 2 * 2^(n+1) * B^n := by positivity
    have hsqL : ((Real.sqrt 3)^(n+1))^2 = 3^(n+1) := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    have hsqR : (2 * 2^(n+1) * B^n)^2 = 4 * 4^(n+1) * B2^n := by
      have h1 : ((B:ℝ)^n)^2 = B2^n := by rw [← pow_mul, mul_comm, pow_mul, hBsq]
      have h2 : ((2:ℝ)^(n+1))^2 = 4^(n+1) := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [mul_pow, mul_pow, h1, h2]; norm_num
    have hB2eq : B2 = (3/4) * (1 - 1/(2*D)) := by rw [hB2_def, hA_def]; field_simp; ring
    have hbern : (1/2:ℝ) ≤ (1 - 1/(2*D))^n := by
      have h := one_add_mul_le_pow (a := -(1/(2*D))) (by
        have : 0 < 1/(2*D) := by positivity
        linarith) n
      have hcast : (1 : ℝ) + (n:ℝ) * (-(1/(2*D))) = 1 - (n:ℝ)/(2*D) := by ring
      rw [hcast] at h
      have hfrac : (n:ℝ)/(2*D) ≤ 1/2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*D), hD]; linarith
      have h2 : (1:ℝ) - (n:ℝ)/(2*D) ≥ 1/2 := by linarith
      have : (1 : ℝ) + -(1/(2*D)) = 1 - 1/(2*D) := by ring
      rw [this] at h
      linarith
    have hsq : ((Real.sqrt 3)^(n+1))^2 ≤ (2 * 2^(n+1) * B^n)^2 := by
      rw [hsqL, hsqR, hB2eq, mul_pow]
      have : (4:ℝ) * 4^(n+1) * ((3/4)^n * (1 - 1/(2*D))^n)
          = 16 * (4^n * (3/4)^n) * (1 - 1/(2*D))^n := by ring
      rw [this, ← mul_pow, show (4:ℝ)*(3/4) = 3 by norm_num, pow_succ]
      nlinarith [hbern, pow_pos (by norm_num : (0:ℝ) < 3) n]
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hL0, Real.sqrt_sq hR0] at this
  -- combine
  set M' : ℕ := 16 * (n+1) * 2^(n+1) with hM'
  have hM'R : (M' : ℝ) = 16 * ((n:ℝ)+1) * 2^(n+1) := by rw [hM']; push_cast; ring
  have hkey' : (Real.sqrt 3)^(n+1) ≤ (M':ℝ) * (A * B^n) := by rw [hM'R]; exact hkey
  have hpack := packing_ennreal n k q hq hthin
  have h1 : ENNReal.ofReal ((Real.sqrt 3)^(n+1))
      ≤ (M' : ℝ≥0∞) * ENNReal.ofReal (A * B^n) := by
    rw [← ENNReal.ofReal_natCast M', ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hkey'
  have hstep : (Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal (A * B^n) * V)
      ≤ ((M' * k : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (A * B^n) * V) := by
    calc (Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal (A * B^n) * V)
        ≤ (Fintype.card ι : ℝ≥0∞) * volume (cap n) :=
          mul_le_mul' le_rfl (by rw [← hcb1]; exact hcap)
      _ ≤ (k : ℝ≥0∞) * volume (closedBall (0:EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt 3)) := hpack
      _ = (k : ℝ≥0∞) * (ENNReal.ofReal ((Real.sqrt 3)^(n+1)) * V) := by rw [hcb3]
      _ ≤ (k : ℝ≥0∞) * (((M':ℝ≥0∞) * ENNReal.ofReal (A * B^n)) * V) :=
          mul_le_mul' le_rfl (mul_le_mul' h1 le_rfl)
      _ = ((M' * k : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (A * B^n) * V) := by push_cast; ring
  have hne0 : ENNReal.ofReal (A * B^n) * V ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨(ENNReal.ofReal_pos.mpr (by positivity)).ne', hV0⟩
  have hnetop : ENNReal.ofReal (A * B^n) * V ≠ ⊤ := by
    simp [ENNReal.mul_ne_top, hVtop]
  rw [mul_comm (Fintype.card ι : ℝ≥0∞), mul_comm (((M' * k : ℕ)) : ℝ≥0∞)] at hstep
  have hfin := (ENNReal.mul_le_mul_iff_right hne0 hnetop).mp hstep
  have : Fintype.card ι ≤ M' * k := by exact_mod_cast hfin
  rw [hM'] at this
  exact this


/-- **Main theorem.** Every finite `k`-thin collection of closed balls of positive radius in
`ℝ^d` (`d ≥ 1`) contains a ball meeting at most `16 * d * 2 ^ d * k` of the others. -/
theorem degree_le (d k N : ℕ) (hd : 1 ≤ d) (hN : 0 < N)
    (x : Fin N → EuclideanSpace ℝ (Fin d)) (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i)
    (hthin : ∀ p : EuclideanSpace ℝ (Fin d),
        {i : Fin N | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) :
    ∃ i₀ : Fin N,
      {i : Fin N | i ≠ i₀ ∧
          (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
        ≤ 16 * d * 2 ^ d * k := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ r ⟨Classical.arbitrary (Fin N), Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  set r0 : ℝ := r i₀ with hr0_def
  have hr0 : 0 < r0 := hr i₀
  set S : Set (Fin N) := {i : Fin N | i ≠ i₀ ∧
      (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty} with hS
  -- geometric data
  set v : Fin N → EuclideanSpace ℝ (Fin (n+1)) := fun i => x i - x i₀ with hv
  set Dd : Fin N → ℝ := fun i => ‖v i‖ with hDd
  set aa : Fin N → ℝ := fun i => r i - r0 with haa
  set lam : Fin N → ℝ := fun i => (max 0 (Dd i - aa i)) / Dd i with hlam
  set w : Fin N → EuclideanSpace ℝ (Fin (n+1)) := fun i => lam i • v i with hw
  set q : Fin N → EuclideanSpace ℝ (Fin (n+1)) := fun i => r0⁻¹ • w i with hq
  have haa0 : ∀ i, 0 ≤ aa i := fun i => sub_nonneg.mpr (hmin i (Finset.mem_univ i))
  have hDd0 : ∀ i, 0 ≤ Dd i := fun i => norm_nonneg _
  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i; rw [hlam]; exact div_nonneg (le_max_left _ _) (hDd0 i)
  have hlam1 : ∀ i, lam i ≤ 1 := by
    intro i
    rw [hlam]
    rcases eq_or_lt_of_le (hDd0 i) with h | h
    · simp [← h]
    · rw [div_le_one h]
      exact max_le (hDd0 i) (by linarith [haa0 i])
  have hwn : ∀ i, ‖w i‖ = max 0 (Dd i - aa i) := by
    intro i
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hlam0 i)]
    show lam i * Dd i = max 0 (Dd i - aa i)
    rw [hlam]
    rcases eq_or_lt_of_le (hDd0 i) with h | h
    · rw [← h, mul_zero, zero_sub, max_eq_left (by linarith [haa0 i] : -aa i ≤ 0)]
    · field_simp
  have hwv : ∀ i, ‖w i - v i‖ ≤ aa i := by
    intro i
    have : w i - v i = (lam i - 1) • v i := by rw [hw]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hlam1 i])]
    show -(lam i - 1) * Dd i ≤ aa i
    rcases eq_or_lt_of_le (hDd0 i) with h | h
    · rw [← h]; simp [haa0 i]
    · rw [hlam]
      have : (-((max 0 (Dd i - aa i)) / Dd i) + 1) * Dd i = Dd i - max 0 (Dd i - aa i) := by
        field_simp; ring
      rw [show -(max 0 (Dd i - aa i) / Dd i - 1) = -(max 0 (Dd i - aa i) / Dd i) + 1 by ring, this]
      rcases le_total (Dd i - aa i) 0 with h2 | h2
      · rw [max_eq_left h2]; linarith
      · rw [max_eq_right h2]; linarith
  -- the reduced family
  haveI : Fintype ↥S := Set.Finite.fintype (Set.toFinite S)
  have hqle : ∀ j : ↥S, ‖q (j : Fin N)‖ ≤ 2 := by
    rintro ⟨i, hi1, hi2⟩
    obtain ⟨z, hz1, hz2⟩ := hi2
    have hDle : Dd i ≤ r i + r0 := by
      have : ‖v i‖ ≤ ‖x i - z‖ + ‖z - x i₀‖ := by
        rw [hv]; simpa using norm_sub_le_norm_sub_add_norm_sub (x i) z (x i₀)
      have h1 : ‖x i - z‖ ≤ r i := by
        rw [← dist_eq_norm, dist_comm]; exact Metric.mem_closedBall.mp hz1
      have h2 : ‖z - x i₀‖ ≤ r0 := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz2
      rw [hDd]; linarith
    have : ‖w i‖ ≤ 2 * r0 := by
      rw [hwn i]
      exact max_le (by linarith) (by rw [haa]; linarith)
    rw [hq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0]
    rw [inv_mul_le_iff₀ hr0]
    linarith
  have hthin' : ∀ y : EuclideanSpace ℝ (Fin (n+1)),
      {j : ↥S | dist y (q (j : Fin N)) ≤ 1}.ncard ≤ k := by
    intro y
    set Y : EuclideanSpace ℝ (Fin (n+1)) := x i₀ + r0 • y with hY
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun j => (j : Fin N)) ?_ ?_ (Set.toFinite _))
      (hthin Y)
    · rintro ⟨i, hi⟩ hj
      simp only [Set.mem_setOf_eq] at hj ⊢
      have hqi : r0 • q i = w i := by
        rw [hq, smul_smul, mul_inv_cancel₀ (ne_of_gt hr0), one_smul]
      have hYx : Y - x i = r0 • (y - q i) + (w i - v i) := by
        rw [hY, hv, ← hqi]; module
      rw [Metric.mem_closedBall, dist_eq_norm, hYx]
      have h1 : ‖r0 • (y - q i)‖ ≤ r0 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
        have := hj
        rw [dist_eq_norm] at this
        nlinarith [norm_nonneg (y - q i)]
      calc ‖r0 • (y - q i) + (w i - v i)‖ ≤ ‖r0 • (y - q i)‖ + ‖w i - v i‖ := norm_add_le _ _
        _ ≤ r0 + aa i := by linarith [hwv i]
        _ = r i := by rw [haa]; ring
    · intro j1 _ j2 _ h; exact Subtype.ext h
  have hcard := card_le n k (fun j : ↥S => q (j : Fin N)) hqle hthin'
  have hSc : S.ncard = Fintype.card ↥S := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [hSc]
  exact hcard

/-- The proposition of `Statements.PlyUpperTwoPowD`, proved. -/
theorem proof :
    ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
      ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        (∀ p : EuclideanSpace ℝ (Fin d),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀ : Fin n,
          {i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
            ≤ 16 * d * 2 ^ d * k :=
  fun d k n hd hn x r hr hthin => degree_le d k n hd hn x r hr hthin

end Submissions.PlyUpperTwoPowD.RateTwo
