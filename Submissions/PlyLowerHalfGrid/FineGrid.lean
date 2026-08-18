import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
open MeasureTheory Metric Set
open scoped ENNReal

namespace Submissions.PlyLowerHalfGrid.FineGrid

lemma norm_sq_eq (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ‖u‖^2 = ∑ i, (u.ofLp i)^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  simp [sq_abs]

noncomputable def vv (m : ℕ) : ℝ := (Real.sqrt Real.pi)^m / Real.Gamma ((m:ℝ)/2 + 1)

lemma vv_pos (m : ℕ) : 0 < vv m :=
  div_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))

lemma volume_cb (m : ℕ) (hm : 1 ≤ m) (x : EuclideanSpace ℝ (Fin m)) (rr : ℝ) (hrr : 0 ≤ rr) :
    volume (closedBall x rr) = ENNReal.ofReal (rr^m * vv m) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, vv,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hrr]

/-- The lattice `ℤ^d` inside `ℝ^d`. -/
noncomputable def emb (d : ℕ) (z : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (z i : ℝ))

lemma emb_apply (d : ℕ) (z : Fin d → ℤ) (i : Fin d) : (emb d z).ofLp i = (z i : ℝ) := rfl

lemma emb_injective (d : ℕ) : Function.Injective (emb d) := by
  intro z z' h
  funext i
  have := congrArg (fun u => (WithLp.ofLp u) i) h
  simpa [emb_apply] using this

lemma abs_coord_le (d : ℕ) (u : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |u.ofLp i| ≤ ‖u‖ := by
  have h : (u.ofLp i)^2 ≤ ‖u‖^2 := by
    rw [norm_sq_eq]
    exact Finset.single_le_sum (f := fun j => (u.ofLp j)^2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [abs_nonneg (u.ofLp i), norm_nonneg u, sq_abs (u.ofLp i)]

/-- The half-open unit cube centred at the origin. -/
def Qb (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x.ofLp i ∈ Set.Ico (-(1/2) : ℝ) (1/2)}

lemma Qb_norm (d : ℕ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Qb d) :
    ‖x‖ ≤ Real.sqrt d / 2 := by
  have h : ‖x‖^2 ≤ (d : ℝ)/4 := by
    rw [norm_sq_eq]
    calc ∑ i, (x.ofLp i)^2 ≤ ∑ _i : Fin d, ((1:ℝ)/4) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have := hx i
          simp only [Set.mem_Ico] at this
          nlinarith [this.1, this.2]
      _ = (d:ℝ)/4 := by simp; ring
  have hsd : (Real.sqrt (d:ℝ))^2 = (d:ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
  nlinarith [norm_nonneg x, Real.sqrt_nonneg (d:ℝ), h, hsd]


lemma Qb_vol (d : ℕ) : volume (Qb d) = 1 := by
  have hpre : Qb d = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin d => Set.Ico (-(1/2) : ℝ) (1/2))) := by
    ext x; simp [Qb, Set.mem_pi]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet)]
  rw [volume_pi_pi]
  simp only [Real.volume_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show -(1/2 : ℝ) = -(2:ℝ)⁻¹ by norm_num, show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num,
    sub_neg_eq_add, show (2:ℝ)⁻¹ + (2:ℝ)⁻¹ = 1 by norm_num]
  simp

lemma cube_disjoint (d : ℕ) {z z' : Fin d → ℤ} (h : z ≠ z')
    (x : EuclideanSpace ℝ (Fin d)) (hx : x - emb d z ∈ Qb d) (hx' : x - emb d z' ∈ Qb d) :
    False := by
  apply h
  funext i
  have h1 := hx i
  have h2 := hx' i
  simp only [Set.mem_Ico] at h1 h2
  have e1 : (x - emb d z).ofLp i = x.ofLp i - (z i : ℝ) := rfl
  have e2 : (x - emb d z').ofLp i = x.ofLp i - (z' i : ℝ) := rfl
  rw [e1] at h1; rw [e2] at h2
  have b1 : (z i - z' i : ℤ) < 1 := by
    have hr : ((z i - z' i : ℤ) : ℝ) < 1 := by push_cast; linarith [h1.1, h1.2, h2.1, h2.2]
    exact_mod_cast hr
  have b2 : (-1:ℤ) < z i - z' i := by
    have hr : (-1:ℝ) < ((z i - z' i : ℤ) : ℝ) := by push_cast; linarith [h1.1, h1.2, h2.1, h2.2]
    exact_mod_cast hr
  omega

lemma cube_cover (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ z : Fin d → ℤ, x - emb d z ∈ Qb d := by
  refine ⟨fun i => ⌊x.ofLp i + 1/2⌋, fun i => ?_⟩
  have e1 : (x - emb d (fun i => ⌊x.ofLp i + 1/2⌋)).ofLp i = x.ofLp i - (⌊x.ofLp i + 1/2⌋ : ℝ) := rfl
  rw [e1]
  have h1 := Int.floor_le (x.ofLp i + 1/2)
  have h2 := Int.lt_floor_add_one (x.ofLp i + 1/2)
  simp only [Set.mem_Ico]
  constructor <;> linarith


lemma Qb_meas (d : ℕ) : MeasurableSet (Qb d) := by
  have hpre : Qb d = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin d => Set.Ico (-(1/2) : ℝ) (1/2))) := by
    ext x; simp [Qb, Set.mem_pi]
  rw [hpre]
  exact (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

def cube (d : ℕ) (z : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) := {x | x - emb d z ∈ Qb d}

lemma cube_meas (d : ℕ) (z : Fin d → ℤ) : MeasurableSet (cube d z) := by
  have : cube d z = (fun x => -(emb d z) + x) ⁻¹' (Qb d) := by
    ext x; simp [cube, sub_eq_neg_add, add_comm]
  rw [this]
  exact (Qb_meas d).preimage (measurable_const_add _)

lemma cube_vol (d : ℕ) (z : Fin d → ℤ) : volume (cube d z) = 1 := by
  have h : cube d z = (fun x => -(emb d z) + x) ⁻¹' (Qb d) := by
    ext x; simp [cube, sub_eq_neg_add, add_comm]
  rw [h, measure_preimage_add, Qb_vol]

lemma cube_pd (d : ℕ) (U : Finset (Fin d → ℤ)) :
    (U : Set (Fin d → ℤ)).PairwiseDisjoint (cube d) := by
  intro z _ z' _ hzz'
  refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
  exact cube_disjoint d hzz' x hx hx'

/-- Upper bound: a set of lattice points inside a ball is no larger than the volume of the
slightly larger ball. -/
lemma count_upper (d : ℕ) (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d)) (s : ℝ) (hs : 0 ≤ s)
    (U : Finset (Fin d → ℤ)) (hU : ∀ z ∈ U, ‖emb d z - y‖ ≤ s) :
    (U.card : ℝ) ≤ (s + Real.sqrt d/2)^d * vv d := by
  have hsub : (⋃ z ∈ U, cube d z) ⊆ closedBall y (s + Real.sqrt d/2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, hz, hxz⟩ := hx
    have h1 : ‖x - emb d z‖ ≤ Real.sqrt d/2 := Qb_norm d hxz
    have h2 : ‖emb d z - y‖ ≤ s := hU z hz
    simp only [Metric.mem_closedBall, dist_eq_norm]
    calc ‖x - y‖ = ‖(x - emb d z) + (emb d z - y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - emb d z‖ + ‖emb d z - y‖ := norm_add_le _ _
      _ ≤ Real.sqrt d/2 + s := add_le_add h1 h2
      _ = s + Real.sqrt d/2 := by ring
  have heq : volume (⋃ z ∈ U, cube d z) = (U.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset (cube_pd d U) (fun z _ => cube_meas d z)]
    simp [cube_vol]
  have hle : (U.card : ℝ≥0∞) ≤ ENNReal.ofReal ((s + Real.sqrt d/2)^d * vv d) := by
    rw [← heq, ← volume_cb d hd y _ (by positivity)]
    exact measure_mono hsub
  rw [← ENNReal.ofReal_natCast U.card] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (vv_pos d).le)).mp hle

/-- Lower bound: a set covered by the cubes of `U` has volume at most `U.card`. -/
lemma count_lower (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (U : Finset (Fin d → ℤ))
    (hcov : ∀ x ∈ S, ∃ z ∈ U, x ∈ cube d z) :
    volume S ≤ (U.card : ℝ≥0∞) := by
  have hsub : S ⊆ ⋃ z ∈ U, cube d z := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := hcov x hx
    simp only [Set.mem_iUnion]
    exact ⟨z, hz, hxz⟩
  calc volume S ≤ volume (⋃ z ∈ U, cube d z) := measure_mono hsub
    _ ≤ ∑ z ∈ U, volume (cube d z) := measure_biUnion_finset_le _ _
    _ = (U.card : ℝ≥0∞) := by simp [cube_vol]


lemma ncard_equiv {α β : Type*} (e : α ≃ β) (P : α → Prop) :
    {b : β | P (e.symm b)}.ncard = {a : α | P a}.ncard := by
  have h : {b : β | P (e.symm b)} = e '' {a | P a} := by
    ext b
    constructor
    · intro h; exact ⟨e.symm b, h, by simp⟩
    · rintro ⟨a, ha, rfl⟩; simpa using ha
  rw [h, Set.ncard_image_of_injective _ e.injective]

/-- Half of a ball has at least half its volume. -/
lemma halfball (d : ℕ) (hd : 1 ≤ d) (w e : EuclideanSpace ℝ (Fin d)) (s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal (s^d * vv d)
      ≤ 2 * volume {y : EuclideanSpace ℝ (Fin d) | ‖y - w‖ ≤ s ∧ inner ℝ (y - w) e ≤ 0} := by
  set A : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ‖y - w‖ ≤ s ∧ inner ℝ (y - w) e ≤ 0} with hA
  set A' : Set (EuclideanSpace ℝ (Fin d)) :=
    {y | ‖y - w‖ ≤ s ∧ (0:ℝ) ≤ inner ℝ (y - w) e} with hA'
  have hcover : closedBall w s ⊆ A ∪ A' := by
    intro y hy
    have hn : ‖y - w‖ ≤ s := by simpa [dist_eq_norm] using hy
    rcases le_total (inner ℝ (y - w) e : ℝ) 0 with h | h
    · exact Or.inl ⟨hn, h⟩
    · exact Or.inr ⟨hn, h⟩
  have hAA' : volume A' = volume A := by
    have hpre : A' = (fun y => -y) ⁻¹' ((fun x => (2:ℝ) • w + x) ⁻¹' A) := by
      ext y
      have h1 : ((2:ℝ) • w + -y) - w = -(y - w) := by module
      simp only [Set.mem_preimage, hA, hA', Set.mem_setOf_eq, h1, norm_neg, inner_neg_left]
      constructor
      · rintro ⟨h2, h3⟩; exact ⟨h2, by linarith⟩
      · rintro ⟨h2, h3⟩; exact ⟨h2, by linarith⟩
    rw [hpre, Measure.measure_preimage_neg, measure_preimage_add]
  have hball : volume (closedBall w s) ≤ volume A + volume A' :=
    le_trans (measure_mono hcover) (measure_union_le _ _)
  rw [volume_cb d hd w s hs] at hball
  rw [two_mul]
  calc ENNReal.ofReal (s^d * vv d) ≤ volume A + volume A' := hball
    _ = volume A + volume A := by rw [hAA']


lemma balls_meet (d : ℕ) (p q : EuclideanSpace ℝ (Fin d)) (rr : ℝ) (hrr : 0 ≤ rr) :
    (closedBall p rr ∩ closedBall q rr).Nonempty ↔ ‖p - q‖ ≤ 2*rr := by
  constructor
  · rintro ⟨y, hy1, hy2⟩
    simp only [Metric.mem_closedBall, dist_eq_norm] at hy1 hy2
    calc ‖p - q‖ = ‖(p - y) + (y - q)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖p - y‖ + ‖y - q‖ := norm_add_le _ _
      _ ≤ rr + rr := by
          refine add_le_add ?_ ?_
          · rw [← norm_neg]; simpa using hy1
          · simpa using hy2
      _ = 2*rr := by ring
  · intro h
    refine ⟨(2:ℝ)⁻¹ • (p + q), ?_, ?_⟩
    · simp only [Metric.mem_closedBall, dist_eq_norm]
      have : (2:ℝ)⁻¹ • (p + q) - p = (2:ℝ)⁻¹ • (q - p) := by module
      rw [this, norm_smul]
      simp only [norm_inv, Real.norm_ofNat]
      rw [← norm_neg (q - p), neg_sub]
      linarith
    · simp only [Metric.mem_closedBall, dist_eq_norm]
      have : (2:ℝ)⁻¹ • (p + q) - q = (2:ℝ)⁻¹ • (p - q) := by module
      rw [this, norm_smul]
      simp only [norm_inv, Real.norm_ofNat]
      linarith

/-- Transport a construction indexed by an arbitrary finite type to one indexed by `Fin n`. -/
lemma transport {ι : Type} [Fintype ι] (d : ℕ) (x : ι → EuclideanSpace ℝ (Fin d)) (r : ι → ℝ)
    (k c C : ℕ) (hne : Nonempty ι)
    (h1 : ∀ i, 0 < r i) (h2 : Function.Injective (fun i => (x i, r i)))
    (h3 : ∀ p : EuclideanSpace ℝ (Fin d),
      {i : ι | p ∈ closedBall (x i) (r i)}.ncard ≤ k)
    (h4 : ∀ i₀ : ι, c*k + C <
      {i : ι | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty}.ncard) :
    ∃ (n : ℕ) (x' : Fin n → EuclideanSpace ℝ (Fin d)) (r' : Fin n → ℝ),
      0 < n ∧ (∀ i, 0 < r' i) ∧ Function.Injective (fun i => (x' i, r' i)) ∧
      (∀ p : EuclideanSpace ℝ (Fin d),
        {i : Fin n | p ∈ closedBall (x' i) (r' i)}.ncard ≤ k) ∧
      (∀ i₀ : Fin n, c*k + C <
        {i : Fin n | i ≠ i₀ ∧
          (closedBall (x' i) (r' i) ∩ closedBall (x' i₀) (r' i₀)).Nonempty}.ncard) := by
  classical
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun j => x (e.symm j), fun j => r (e.symm j), ?_, ?_, ?_, ?_, ?_⟩
  · exact Fintype.card_pos
  · intro j; exact h1 _
  · intro j j' hjj'
    have : e.symm j = e.symm j' := h2 hjj'
    simpa using congrArg e this
  · intro p
    rw [ncard_equiv e (fun i => p ∈ closedBall (x i) (r i))]
    exact h3 p
  · intro j₀
    set P : ι → Prop := fun i => i ≠ e.symm j₀ ∧
      (closedBall (x i) (r i) ∩ closedBall (x (e.symm j₀)) (r (e.symm j₀))).Nonempty with hP
    have hset : {j : Fin (Fintype.card ι) | j ≠ j₀ ∧
        (closedBall (x (e.symm j)) (r (e.symm j)) ∩
          closedBall (x (e.symm j₀)) (r (e.symm j₀))).Nonempty}
        = {j : Fin (Fintype.card ι) | P (e.symm j)} := by
      ext j
      simp only [Set.mem_setOf_eq, hP]
      exact and_congr_left (fun _ => (e.symm.injective.ne_iff).symm)
    rw [hset, ncard_equiv e P]
    exact h4 (e.symm j₀)

/-- The unit vector in the direction of `p` (zero if `p = 0`). -/
noncomputable def dir (d : ℕ) (p : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if p = 0 then 0 else ‖p‖⁻¹ • p

lemma dir_norm_le (d : ℕ) (p : EuclideanSpace ℝ (Fin d)) : ‖dir d p‖ ≤ 1 := by
  rw [dir]; split_ifs with h
  · simp
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma dir_inner (d : ℕ) (p u : EuclideanSpace ℝ (Fin d)) :
    inner ℝ p u = ‖p‖ * inner ℝ (dir d p) u := by
  rw [dir]; split_ifs with h
  · simp [h]
  · rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_mul]

lemma dir_self (d : ℕ) (p : EuclideanSpace ℝ (Fin d)) :
    ‖p - ‖p‖ • dir d p‖ = 0 := by
  rw [dir]; split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul, sub_self, norm_zero]

/-- The geometric core of the lower-bound construction. -/
lemma geo (d : ℕ) (p₀ : EuclideanSpace ℝ (Fin d)) (aa c0 ss MM : ℝ)
    (haa : 0 ≤ aa) (hc0 : c0 = aa + 2) (hss : 0 ≤ ss)
    (ht : ‖p₀‖ ≤ MM) (hMM : 2*c0 ≤ MM)
    (hkey : 2*c0*ss + ss^2 ≤ 4*MM - 2*aa - 2*c0)
    (y : EuclideanSpace ℝ (Fin d))
    (hy1 : ‖y - (p₀ - c0 • dir d p₀)‖ ≤ ss)
    (hy2 : inner ℝ (y - (p₀ - c0 • dir d p₀)) (dir d p₀) ≤ 0) :
    ‖y‖ ≤ MM - aa ∧ ‖y - p₀‖ ≤ ss + c0 := by
  have hc0pos : 0 < c0 := by rw [hc0]; linarith
  obtain ⟨e, he⟩ : ∃ e, e = dir d p₀ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = p₀ - c0 • e := ⟨_, rfl⟩
  rw [← he, ← hw] at hy1 hy2
  have hepos : ‖e‖ ≤ 1 := by rw [he]; exact dir_norm_le d p₀
  have hpe : ∀ u, inner ℝ p₀ u = ‖p₀‖ * inner ℝ e u := by
    intro u; rw [he]; exact dir_inner d p₀ u
  have hwp : ‖w - p₀‖ ≤ c0 := by
    have hd1 : w - p₀ = -(c0 • e) := by rw [hw]; module
    rw [hd1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hc0pos]
    nlinarith [norm_nonneg e]
  refine ⟨?_, ?_⟩
  · obtain ⟨sg, hsg⟩ : ∃ sg : ℝ, sg = inner ℝ (y - w) e := ⟨_, rfl⟩
    rw [← hsg] at hy2
    have hsgabs : |sg| ≤ ss := by
      rw [hsg]
      calc |inner ℝ (y - w) e| ≤ ‖y - w‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ ≤ ss * 1 := mul_le_mul hy1 hepos (norm_nonneg _) hss
        _ = ss := by ring
    have hcomm : inner ℝ e (y - w) = sg := by rw [hsg]; exact (real_inner_comm e (y - w)).symm
    have hstep : inner ℝ w (y - w) = inner ℝ (p₀ - c0 • e) (y - w) := by rw [hw]
    have h1 : inner ℝ (p₀ - c0 • e) (y - w) = (‖p₀‖ - c0) * sg := by
      rw [inner_sub_left, real_inner_smul_left, hpe (y - w), hcomm]
      ring
    have hinner : inner ℝ w (y - w) ≤ c0 * ss := by
      rw [hstep, h1]
      have h2 : ‖p₀‖ * sg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hy2
      have h3 : -sg ≤ ss := by cases abs_le.mp hsgabs with | intro l r => linarith
      nlinarith
    have hwnorm : ‖w‖ ≤ MM - c0 := by
      by_cases hp : p₀ = 0
      · have he0 : e = 0 := by rw [he, dir, if_pos hp]
        have hw0 : w = 0 := by rw [hw, he0, hp]; simp
        rw [hw0, norm_zero]; linarith
      · have henorm : ‖e‖ = 1 := by
          rw [he, dir, if_neg hp, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]
        have hpee : inner ℝ p₀ e = ‖p₀‖ := by
          rw [hpe e, real_inner_self_eq_norm_mul_norm, henorm]; ring
        have hsq : ‖w‖^2 = (‖p₀‖ - c0)^2 := by
          have h1' : ‖w‖ = ‖p₀ - c0 • e‖ := by rw [hw]
          rw [h1', norm_sub_sq_real, real_inner_smul_right, hpee, norm_smul, Real.norm_eq_abs,
            abs_of_pos hc0pos, henorm]
          ring
        nlinarith [norm_nonneg w, norm_nonneg p₀, hsq, ht, hMM, hc0pos]
    have hy2n : ‖y‖^2 = ‖w‖^2 + 2 * inner ℝ w (y - w) + ‖y - w‖^2 := by
      have h := norm_add_sq_real w (y - w)
      rw [show w + (y - w) = y by module] at h
      exact h
    have hMMc : 0 ≤ MM - c0 := by linarith
    have hA : ‖w‖^2 ≤ (MM - c0)^2 := by nlinarith [norm_nonneg w]
    have hB : ‖y - w‖^2 ≤ ss^2 := by nlinarith [norm_nonneg (y - w)]
    have hyle : ‖y‖^2 ≤ (MM - aa)^2 := by nlinarith [hy2n, hA, hB, hinner, hkey]
    nlinarith [norm_nonneg y, hyle, haa, hMM, hc0pos]
  · calc ‖y - p₀‖ = ‖(y - w) + (w - p₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - w‖ + ‖w - p₀‖ := norm_add_le _ _
      _ ≤ ss + c0 := add_le_add hy1 hwp

lemma ncard_subtype {α : Type*} (T : Set α) (P : α → Prop) :
    {i : ↥T | P i.val}.ncard = {z | z ∈ T ∧ P z}.ncard := by
  have h : Subtype.val '' {i : ↥T | P i.val} = {z | z ∈ T ∧ P z} := by
    ext z
    constructor
    · rintro ⟨⟨z', hz'⟩, hp, rfl⟩; exact ⟨hz', hp⟩
    · rintro ⟨hz, hp⟩; exact ⟨⟨z, hz⟩, hp, rfl⟩
  rw [← h, Set.ncard_image_of_injective _ Subtype.val_injective]

lemma ncard_to_finset {α : Type*} [DecidableEq α] (T : Set α) (hT : T.Finite) (P : α → Prop)
    [DecidablePred P] :
    {z | z ∈ T ∧ P z}.ncard = ((hT.toFinset).filter P).card := by
  have hfin : {z | z ∈ T ∧ P z}.Finite := hT.subset (fun z hz => hz.1)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  congr 1
  ext z; simp

set_option maxHeartbeats 1000000 in
theorem lower_bound (d c C : ℕ) (hd : 1 ≤ d) (hc : 2 * c < 2 ^ d) :
    ∃ (k n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
      0 < n ∧ (∀ i, 0 < r i) ∧ Function.Injective (fun i => (x i, r i)) ∧
      (∀ p : EuclideanSpace ℝ (Fin d),
        {i : Fin n | p ∈ closedBall (x i) (r i)}.ncard ≤ k) ∧
      (∀ i₀ : Fin n, c * k + C <
        {i : Fin n | i ≠ i₀ ∧
          (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty}.ncard) := by
  classical
  obtain ⟨aa, haa_def⟩ : ∃ aa : ℝ, aa = Real.sqrt d / 2 := ⟨_, rfl⟩
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have haa0 : 0 ≤ aa := by rw [haa_def]; positivity
  have haad : aa ≤ (d:ℝ)/2 := by
    rw [haa_def]
    have : Real.sqrt d ≤ (d:ℝ) := by
      nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ (d:ℝ)), Real.sqrt_nonneg (d:ℝ), hdR]
    linarith
  obtain ⟨c0, hc0_def⟩ : ∃ c0 : ℝ, c0 = aa + 2 := ⟨_, rfl⟩
  -- the scale
  obtain ⟨m, hmA, hmB, hmC, hm1⟩ :
      ∃ m : ℕ, ((d:ℝ) + 3 ≤ m) ∧ ((2:ℝ)^(d+1) * d * (2*aa+1) ≤ m) ∧
        (2*((c:ℝ)+C+2) ≤ m * vv d) ∧ 1 ≤ m := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max ((d:ℝ)+3)
      (max ((2:ℝ)^(d+1) * d * (2*aa+1)) (2*((c:ℝ)+C+2)/vv d)))
    refine ⟨N, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_left _ _) hN
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    · have h := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
      rw [div_le_iff₀ (vv_pos d)] at h
      exact h
    · have : (1:ℝ) ≤ (N:ℝ) := by
        have := le_trans (le_max_left _ _) hN
        linarith
      exact_mod_cast this
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  obtain ⟨MM, hMM_def⟩ : ∃ MM : ℝ, MM = ((m:ℝ) + d + 3)^2 := ⟨_, rfl⟩
  obtain ⟨ss, hss_def⟩ : ∃ ss : ℝ, ss = 2*(m:ℝ) - 2*aa - 2 := ⟨_, rfl⟩
  have hss0 : 0 ≤ ss := by rw [hss_def]; nlinarith [hmA, haad]
  have hssle : ss ≤ 2*(m:ℝ) := by rw [hss_def]; linarith
  have hMM2c0 : 2*c0 ≤ MM := by
    rw [hMM_def, hc0_def]; nlinarith [hmR, hdR, haad]
  have hkey : 2*c0*ss + ss^2 ≤ 4*MM - 2*aa - 2*c0 := by
    rw [hMM_def, hc0_def]
    nlinarith [hmR, hdR, haad, haa0, hss0, hssle]
  -- the lattice point set
  obtain ⟨Tset, hT_def⟩ : ∃ T : Set (Fin d → ℤ), T = {z | ‖emb d z‖ ≤ MM} := ⟨_, rfl⟩
  have hTfin : Tset.Finite := by
    refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (-⌈MM⌉) ⌈MM⌉)) ?_
    intro z hz i _
    rw [hT_def] at hz
    have h1 : |((z i : ℤ) : ℝ)| ≤ MM := by
      have h2 := abs_coord_le d (emb d z) i
      rw [emb_apply] at h2
      exact le_trans h2 hz
    obtain ⟨hl, hr⟩ := abs_le.mp h1
    constructor
    · have h3 : ((-⌈MM⌉ : ℤ) : ℝ) ≤ ((z i : ℤ) : ℝ) := by
        push_cast; linarith [Int.le_ceil MM]
      exact_mod_cast h3
    · have h3 : ((z i : ℤ) : ℝ) ≤ ((⌈MM⌉ : ℤ) : ℝ) := le_trans hr (Int.le_ceil MM)
      exact_mod_cast h3
  haveI : Fintype ↥Tset := hTfin.fintype
  have hembzero : ‖emb d (0 : Fin d → ℤ)‖ = 0 := by
    have h : ‖emb d (0 : Fin d → ℤ)‖^2 = 0 := by rw [norm_sq_eq]; simp [emb_apply]
    nlinarith [norm_nonneg (emb d (0 : Fin d → ℤ))]
  have hMMpos : 0 < MM := by rw [hMM_def]; positivity
  have hTne : (0 : Fin d → ℤ) ∈ Tset := by
    rw [hT_def]; simp only [Set.mem_setOf_eq, hembzero]; linarith
  haveI : Nonempty ↥Tset := ⟨⟨0, hTne⟩⟩
  obtain ⟨k, hk_def⟩ : ∃ k : ℕ, k = ⌈((m:ℝ) + aa)^d * vv d⌉₊ := ⟨_, rfl⟩
  -- thinness
  have hthin : ∀ p : EuclideanSpace ℝ (Fin d),
      {i : ↥Tset | p ∈ closedBall (emb d (i : Fin d → ℤ)) (m:ℝ)}.ncard ≤ k := by
    intro p
    rw [ncard_subtype Tset (fun z => p ∈ closedBall (emb d z) (m:ℝ)),
      ncard_to_finset Tset hTfin]
    have hU : ∀ z ∈ (hTfin.toFinset).filter (fun z => p ∈ closedBall (emb d z) (m:ℝ)),
        ‖emb d z - p‖ ≤ (m:ℝ) := by
      intro z hz
      simp only [Finset.mem_filter, Metric.mem_closedBall, dist_eq_norm] at hz
      calc ‖emb d z - p‖ = ‖p - emb d z‖ := by rw [norm_sub_rev]
        _ ≤ (m:ℝ) := hz.2
    have hcu := count_upper d hd p (m:ℝ) (le_of_lt hm0) _ hU
    rw [hk_def]
    have hfin : ((((hTfin.toFinset).filter
        (fun z => p ∈ closedBall (emb d z) (m:ℝ))).card : ℝ))
        ≤ ((m:ℝ) + aa)^d * vv d := by rw [haa_def]; exact hcu
    have := le_trans hfin (Nat.le_ceil (((m:ℝ) + aa)^d * vv d))
    exact_mod_cast this
  -- degree
  have hdeg : ∀ i₀ : ↥Tset, c*k + C <
      {i : ↥Tset | i ≠ i₀ ∧ (closedBall (emb d (i : Fin d → ℤ)) (m:ℝ) ∩
        closedBall (emb d (i₀ : Fin d → ℤ)) (m:ℝ)).Nonempty}.ncard := by
    intro i₀
    obtain ⟨z₀, hz₀eq⟩ : ∃ z, z = (i₀ : Fin d → ℤ) := ⟨_, rfl⟩
    have hz₀T : z₀ ∈ Tset := by rw [hz₀eq]; exact i₀.2
    have hsetEq : {i : ↥Tset | i ≠ i₀ ∧ (closedBall (emb d (i : Fin d → ℤ)) (m:ℝ) ∩
        closedBall (emb d (i₀ : Fin d → ℤ)) (m:ℝ)).Nonempty}
        = {i : ↥Tset | (fun z => z ≠ z₀ ∧ ‖emb d z - emb d z₀‖ ≤ 2*(m:ℝ)) (i : Fin d → ℤ)} := by
      ext i
      simp only [Set.mem_setOf_eq, ← hz₀eq, balls_meet d _ _ _ (le_of_lt hm0)]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun hcon => h1 (Subtype.ext (by rw [hcon, hz₀eq])), h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun hcon => h1 (by rw [hcon, hz₀eq]), h2⟩
    rw [hsetEq, ncard_subtype Tset (fun z => z ≠ z₀ ∧ ‖emb d z - emb d z₀‖ ≤ 2*(m:ℝ)),
      ncard_to_finset Tset hTfin]
    obtain ⟨V, hV⟩ : ∃ V : Finset (Fin d → ℤ),
        V = (hTfin.toFinset).filter (fun z => ‖emb d z - emb d z₀‖ ≤ 2*(m:ℝ)) := ⟨_, rfl⟩
    obtain ⟨V', hV'⟩ : ∃ V' : Finset (Fin d → ℤ),
        V' = (hTfin.toFinset).filter
          (fun z => z ≠ z₀ ∧ ‖emb d z - emb d z₀‖ ≤ 2*(m:ℝ)) := ⟨_, rfl⟩
    rw [← hV']
    have hVsub : V ⊆ insert z₀ V' := by
      intro z hz
      rw [hV, Finset.mem_filter] at hz
      by_cases hzz : z = z₀
      · rw [hzz]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        rw [hV', Finset.mem_filter]
        exact ⟨hz.1, hzz, hz.2⟩
    have hVcard : V.card ≤ V'.card + 1 :=
      le_trans (Finset.card_le_card hVsub) (Finset.card_insert_le _ _)
    -- the half-ball inside the neighbourhood
    obtain ⟨w, hw⟩ : ∃ w, w = emb d z₀ - c0 • dir d (emb d z₀) := ⟨_, rfl⟩
    obtain ⟨H, hH⟩ : ∃ H : Set (EuclideanSpace ℝ (Fin d)),
        H = {y | ‖y - w‖ ≤ ss ∧ inner ℝ (y - w) (dir d (emb d z₀)) ≤ 0} := ⟨_, rfl⟩
    have hp₀M : ‖emb d z₀‖ ≤ MM := by rw [hT_def] at hz₀T; exact hz₀T
    have hcov : ∀ y ∈ H, ∃ z ∈ V, y ∈ cube d z := by
      intro y hy
      rw [hH] at hy
      obtain ⟨z, hz⟩ := cube_cover d y
      have hnorm : ‖y - emb d z‖ ≤ aa := by rw [haa_def]; exact Qb_norm d hz
      have hnorm' : ‖emb d z - y‖ ≤ aa := by rw [← norm_neg]; simpa using hnorm
      have hgeo := geo d (emb d z₀) aa c0 ss MM haa0 hc0_def hss0 hp₀M hMM2c0 hkey y
        (by rw [← hw]; exact hy.1) (by rw [← hw]; exact hy.2)
      refine ⟨z, ?_, hz⟩
      rw [hV, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨?_, ?_⟩
      · rw [hT_def]
        simp only [Set.mem_setOf_eq]
        calc ‖emb d z‖ = ‖(emb d z - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖emb d z - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ aa + (MM - aa) := add_le_add hnorm' hgeo.1
          _ = MM := by ring
      · calc ‖emb d z - emb d z₀‖ = ‖(emb d z - y) + (y - emb d z₀)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖emb d z - y‖ + ‖y - emb d z₀‖ := norm_add_le _ _
          _ ≤ aa + (ss + c0) := add_le_add hnorm' hgeo.2
          _ = 2*(m:ℝ) := by rw [hss_def, hc0_def]; ring
    have hvolH : volume H ≤ (V.card : ℝ≥0∞) := count_lower d H V hcov
    have hhalf : ENNReal.ofReal (ss^d * vv d) ≤ 2 * volume H := by
      rw [hH]; exact halfball d hd w (dir d (emb d z₀)) ss hss0
    have hVR : ss^d * vv d ≤ 2 * (V.card : ℝ) := by
      have h1 : ENNReal.ofReal (ss^d * vv d) ≤ 2 * (V.card : ℝ≥0∞) :=
        le_trans hhalf (mul_le_mul' le_rfl hvolH)
      have h2 : (2 : ℝ≥0∞) * (V.card : ℝ≥0∞) = ENNReal.ofReal (2 * (V.card:ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
        norm_num
      rw [h2] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    -- arithmetic
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((m:ℝ)+aa)^d * vv d := ⟨_, rfl⟩
    have hBpos : 0 < B := by rw [hB]; exact mul_pos (by positivity) (vv_pos d)
    have hkb : (k:ℝ) ≤ B + 1 := by
      rw [hk_def, hB]
      exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt (mul_pos (by positivity) (vv_pos d))))
    obtain ⟨th, hth⟩ : ∃ th : ℝ, th = (d:ℝ)*(2*aa+1)/(m:ℝ) := ⟨_, rfl⟩
    have hxle : (2*aa+1)/(m:ℝ) ≤ 1 := by
      rw [div_le_one hm0]; nlinarith [hmA, haad, hdR]
    have hx0 : 0 ≤ (2*aa+1)/(m:ℝ) := by positivity
    have hbern : (1:ℝ) - th ≤ (1 - (2*aa+1)/(m:ℝ))^d := by
      have h := one_add_mul_le_pow (a := -((2*aa+1)/(m:ℝ))) (by linarith) d
      rw [show (1:ℝ) + (d:ℝ) * -((2*aa+1)/(m:ℝ)) = 1 - (d:ℝ)*((2*aa+1)/(m:ℝ)) by ring,
        show (1:ℝ) + -((2*aa+1)/(m:ℝ)) = 1 - (2*aa+1)/(m:ℝ) by ring] at h
      rw [hth, mul_div_assoc]
      exact h
    have hmono : 2*(1 - (2*aa+1)/(m:ℝ))*((m:ℝ)+aa) ≤ ss := by
      rw [hss_def]
      have hexp : 2*(1 - (2*aa+1)/(m:ℝ))*((m:ℝ)+aa)
          = 2*(m:ℝ) - 2*aa - 2 - 2*((2*aa+1)/(m:ℝ))*aa := by
        field_simp; ring
      rw [hexp]
      linarith [mul_nonneg hx0 haa0]
    have hsslb : (2:ℝ)^d * ((m:ℝ)+aa)^d * (1 - th) ≤ ss^d := by
      have h1 : (0:ℝ) ≤ 2*(1 - (2*aa+1)/(m:ℝ))*((m:ℝ)+aa) := by
        have : (0:ℝ) ≤ 1 - (2*aa+1)/(m:ℝ) := by linarith
        positivity
      have h2 : (2*(1 - (2*aa+1)/(m:ℝ))*((m:ℝ)+aa))^d ≤ ss^d := pow_le_pow_left₀ h1 hmono d
      have h3 : (2*(1 - (2*aa+1)/(m:ℝ))*((m:ℝ)+aa))^d
          = (2:ℝ)^d * (1 - (2*aa+1)/(m:ℝ))^d * ((m:ℝ)+aa)^d := by
        rw [mul_pow, mul_pow]
      rw [h3] at h2
      have h4 : (2:ℝ)^d * ((m:ℝ)+aa)^d * (1 - th)
          ≤ (2:ℝ)^d * (1 - (2*aa+1)/(m:ℝ))^d * ((m:ℝ)+aa)^d := by
        have hp : (0:ℝ) ≤ (2:ℝ)^d * ((m:ℝ)+aa)^d := by positivity
        calc (2:ℝ)^d * ((m:ℝ)+aa)^d * (1 - th)
            ≤ (2:ℝ)^d * ((m:ℝ)+aa)^d * (1 - (2*aa+1)/(m:ℝ))^d :=
              mul_le_mul_of_nonneg_left hbern hp
          _ = (2:ℝ)^d * (1 - (2*aa+1)/(m:ℝ))^d * ((m:ℝ)+aa)^d := by ring
      linarith
    have hc1 : (c:ℝ) + 1 ≤ (2:ℝ)^d/2 := by
      have hdvd : 2 ∣ 2^d := dvd_pow_self 2 (by omega)
      have h2 : 2*c + 2 ≤ 2^d := by omega
      have : ((2*c + 2 : ℕ) : ℝ) ≤ ((2^d : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
    have hthle : (2:ℝ)^d/2 * th ≤ 1/4 := by
      rw [hth, ← mul_div_assoc, div_le_iff₀ hm0]
      have h2 : (2:ℝ)^(d+1) = 2^d * 2 := by rw [pow_succ]
      have h3 : (2:ℝ)^d * 2 * (d:ℝ) * (2*aa+1) ≤ (m:ℝ) := by rw [← h2]; exact hmB
      nlinarith [h3]
    have hBm : 2*((c:ℝ)+C+2) ≤ B := by
      have h1 : (m:ℝ) ≤ ((m:ℝ)+aa)^d := by
        have hA : (m:ℝ)^d ≤ ((m:ℝ)+aa)^d := pow_le_pow_left₀ (by linarith) (by linarith) d
        have hB2 : (m:ℝ) ≤ (m:ℝ)^d := by
          calc (m:ℝ) = (m:ℝ)^1 := (pow_one _).symm
            _ ≤ (m:ℝ)^d := pow_le_pow_right₀ hmR hd
        linarith
      have h2 : (m:ℝ) * vv d ≤ ((m:ℝ)+aa)^d * vv d :=
        mul_le_mul_of_nonneg_right h1 (vv_pos d).le
      rw [hB]; linarith [hmC]
    have hfinal : ((c*k + C : ℕ) : ℝ) + 1 ≤ (V'.card : ℝ) := by
      push_cast
      have hstep1 : (c:ℝ)*k + C + 2 ≤ (c:ℝ)*B + c + C + 2 := by
        nlinarith [hkb, Nat.cast_nonneg (α := ℝ) c]
      have hstep2 : (c:ℝ)*B + c + C + 2 ≤ ss^d * vv d/2 := by
        have e1 : ss^d * vv d / 2 ≥ (2:ℝ)^d/2 * B * (1 - th) := by
          have := mul_le_mul_of_nonneg_right hsslb (vv_pos d).le
          rw [hB]
          nlinarith [this, vv_pos d]
        have e2 : (2:ℝ)^d/2 * B * (1 - th) = (2:ℝ)^d/2 * B - ((2:ℝ)^d/2 * th) * B := by ring
        have e3 : ((2:ℝ)^d/2 * th) * B ≤ B/4 := by nlinarith [hthle, hBpos]
        have e4 : ((c:ℝ)+1) * B ≤ (2:ℝ)^d/2 * B := mul_le_mul_of_nonneg_right hc1 hBpos.le
        nlinarith [e1, e3, e4, hBm, hBpos]
      have hstep3 : ss^d * vv d/2 ≤ (V.card : ℝ) := by linarith [hVR]
      have hstep4 : (V.card : ℝ) ≤ (V'.card : ℝ) + 1 := by exact_mod_cast hVcard
      linarith
    have : c*k + C + 1 ≤ V'.card := by exact_mod_cast hfinal
    omega
  exact ⟨k, transport d (fun i : ↥Tset => emb d (i : Fin d → ℤ)) (fun _ => (m:ℝ)) k c C
    inferInstance (fun _ => hm0) (by
      intro i j hij
      have : emb d (i : Fin d → ℤ) = emb d (j : Fin d → ℤ) := congrArg Prod.fst hij
      exact Subtype.ext (emb_injective d this)) hthin hdeg⟩

/-- The proposition of `Statements.PlyLowerHalfGrid`, proved. -/
theorem proof :
    ∀ (d c C : ℕ), 1 ≤ d → 2 * c < 2 ^ d →
      ∃ (k n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
        0 < n ∧
        (∀ i, 0 < r i) ∧
        Function.Injective (fun i => (x i, r i)) ∧
        (∀ p : EuclideanSpace ℝ (Fin d),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) ∧
        ∀ i₀ : Fin n,
          c * k + C <
            {i : Fin n | i ≠ i₀ ∧
                (Metric.closedBall (x i) (r i) ∩
                  Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard :=
  fun d c C hd hc => lower_bound d c C hd hc

end Submissions.PlyLowerHalfGrid.FineGrid
