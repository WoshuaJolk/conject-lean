import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Real.Pi.Bounds
open MeasureTheory Metric Set
open scoped ENNReal

namespace Submissions.PlyShellBarrier.AnnulusShell

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


noncomputable def split (n : ℕ) (u : EuclideanSpace ℝ (Fin (n+1))) :
    ℝ × EuclideanSpace ℝ (Fin n) :=
  (u.ofLp 0, WithLp.toLp 2 (fun j : Fin n => u.ofLp j.succ))

lemma split_mp (n : ℕ) : MeasurePreserving (split n) volume volume := by
  have h1 : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin (n+1)) → (Fin (n+1) → ℝ))
      volume volume := PiLp.volume_preserving_ofLp _
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)
      volume volume := volume_preserving_piFinSuccAbove _ 0
  have h3 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)))
      volume volume := by
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin n))
  have : split n = (Prod.map (id : ℝ → ℝ)
      (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)))
      ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ∘ WithLp.ofLp := by
    funext u; rfl
  rw [this]
  exact h3.comp (h2.comp h1)

lemma cyl_vol (n : ℕ) (a b ρ : ℝ) :
    volume {u : EuclideanSpace ℝ (Fin (n+1)) | u.ofLp 0 ∈ Set.Icc a b ∧
        ‖(WithLp.toLp 2 (fun j : Fin n => u.ofLp j.succ) : EuclideanSpace ℝ (Fin n))‖ ≤ ρ}
      = volume (Set.Icc a b) * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ) := by
  have hpre : {u : EuclideanSpace ℝ (Fin (n+1)) | u.ofLp 0 ∈ Set.Icc a b ∧
      ‖(WithLp.toLp 2 (fun j : Fin n => u.ofLp j.succ) : EuclideanSpace ℝ (Fin n))‖ ≤ ρ}
      = (split n) ⁻¹' (Set.Icc a b ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ) := by
    ext u
    simp [split, Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
  rw [hpre, (split_mp n).measure_preimage
    ((measurableSet_Icc.prod measurableSet_closedBall).nullMeasurableSet),
    ]
  exact Measure.prod_prod _ _

lemma gamma_step (D : ℝ) (hD : 1 ≤ D) :
    Real.Gamma ((D+1)/2) ≤ Real.sqrt (2/D) * Real.Gamma (D/2+1) := by
  have hs : (0:ℝ) < D/2 := by linarith
  have ht : (0:ℝ) < D/2 + 1 := by linarith
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hs ht
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  rw [show (1/2 : ℝ) * (D/2) + (1/2) * (D/2 + 1) = (D+1)/2 by ring] at h
  have hGt : (0:ℝ) < Real.Gamma (D/2 + 1) := Real.Gamma_pos_of_pos ht
  have hG1 : Real.Gamma (D/2) = (2/D) * Real.Gamma (D/2 + 1) := by
    rw [Real.Gamma_add_one (ne_of_gt hs)]; field_simp
  rw [hG1, Real.mul_rpow (by positivity) hGt.le, mul_assoc, ← Real.rpow_add hGt] at h
  norm_num at h
  rwa [Real.sqrt_eq_rpow]


/-- The other direction of Gamma log-convexity: `Γ(D/2+1) ≤ √((D+1)/2) · Γ((D+1)/2)`. -/
lemma gamma_step2 (D : ℝ) (hD : 0 < D) :
    Real.Gamma (D/2 + 1) ≤ Real.sqrt ((D+1)/2) * Real.Gamma ((D+1)/2) := by
  have hs : (0:ℝ) < (D+1)/2 := by linarith
  have ht : (0:ℝ) < (D+1)/2 + 1 := by linarith
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hs ht
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  rw [show (1/2 : ℝ) * ((D+1)/2) + (1/2) * ((D+1)/2 + 1) = D/2 + 1 by ring] at h
  have hGs : (0:ℝ) < Real.Gamma ((D+1)/2) := Real.Gamma_pos_of_pos hs
  have hG1 : Real.Gamma ((D+1)/2 + 1) = ((D+1)/2) * Real.Gamma ((D+1)/2) :=
    Real.Gamma_add_one (ne_of_gt hs)
  rw [hG1, Real.mul_rpow (by positivity) hGs.le] at h
  calc Real.Gamma (D/2+1)
      ≤ Real.Gamma ((D+1)/2)^((1:ℝ)/2)
          * (((D+1)/2 : ℝ)^((1:ℝ)/2) * Real.Gamma ((D+1)/2)^((1:ℝ)/2)) := h
    _ = ((D+1)/2 : ℝ)^((1:ℝ)/2)
          * (Real.Gamma ((D+1)/2)^((1:ℝ)/2) * Real.Gamma ((D+1)/2)^((1:ℝ)/2)) := by ring
    _ = ((D+1)/2 : ℝ)^((1:ℝ)/2) * Real.Gamma ((D+1)/2) := by
        rw [← Real.rpow_add hGs]; norm_num
    _ = Real.sqrt ((D+1)/2) * Real.Gamma ((D+1)/2) := by rw [← Real.sqrt_eq_rpow]

lemma vv_step2 (n : ℕ) :
    vv n * Real.sqrt (2*Real.pi) ≤ Real.sqrt ((n:ℝ)+2) * vv (n+1) := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hg := gamma_step2 ((n:ℝ)+1) (by linarith)
  rw [show ((n:ℝ)+1)/2 + 1 = ((n:ℝ)+1)/2 + 1 from rfl] at hg
  have hGn : (0:ℝ) < Real.Gamma ((n:ℝ)/2+1) := Real.Gamma_pos_of_pos (by positivity)
  have hGn1 : (0:ℝ) < Real.Gamma (((n:ℝ)+1)/2+1) := Real.Gamma_pos_of_pos (by positivity)
  have hsp : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  -- hg : Γ(((n+1)/2)+1) ≤ √(((n+1)+1)/2) Γ(((n+1)+1)/2)  i.e. Γ((n+1)/2+1) ≤ √((n+2)/2) Γ(n/2+1)
  rw [show ((n:ℝ)+1+1)/2 = (n:ℝ)/2+1 by ring] at hg
  have hvv1 : vv (n+1) = (Real.sqrt Real.pi)^(n+1) / Real.Gamma (((n:ℝ)+1)/2+1) := by
    rw [vv]; congr 2; push_cast; ring
  have hvvn : vv n = (Real.sqrt Real.pi)^n / Real.Gamma ((n:ℝ)/2+1) := by rw [vv]
  have hkey : Real.sqrt 2 * Real.Gamma (((n:ℝ)+1)/2+1)
      ≤ Real.sqrt ((n:ℝ)+2) * Real.Gamma ((n:ℝ)/2+1) := by
    have h2 : Real.sqrt 2 * Real.sqrt ((n:ℝ)/2+1) = Real.sqrt ((n:ℝ)+2) := by
      rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
    calc Real.sqrt 2 * Real.Gamma (((n:ℝ)+1)/2+1)
        ≤ Real.sqrt 2 * (Real.sqrt ((n:ℝ)/2+1) * Real.Gamma ((n:ℝ)/2+1)) :=
          mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg 2)
      _ = (Real.sqrt 2 * Real.sqrt ((n:ℝ)/2+1)) * Real.Gamma ((n:ℝ)/2+1) := by ring
      _ = Real.sqrt ((n:ℝ)+2) * Real.Gamma ((n:ℝ)/2+1) := by rw [h2]
  have hsp2 : Real.sqrt (2*Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  rw [hvv1, hvvn, div_mul_eq_mul_div, ← mul_div_assoc, div_le_div_iff₀ hGn hGn1, pow_succ, hsp2]
  nlinarith [mul_le_mul_of_nonneg_left hkey (mul_nonneg (pow_nonneg hsp.le n) hsp.le),
    pow_pos hsp n, hsp]

/-- Reassemble a vector from its first coordinate and the rest. -/
noncomputable def unsplit (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
    (p.1, WithLp.ofLp p.2))

lemma unsplit_zero (n : ℕ) (x : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    (unsplit n (x, v)).ofLp 0 = x := rfl

lemma unsplit_succ (n : ℕ) (x : ℝ) (v : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (unsplit n (x, v)).ofLp j.succ = v.ofLp j := rfl

lemma unsplit_mp (n : ℕ) : MeasurePreserving (unsplit n) volume volume := by
  have h1 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)))
      volume volume := (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_ofLp (Fin n))
  have h2 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm _
  have h3 : MeasurePreserving
      (WithLp.toLp 2 : (Fin (n+1) → ℝ) → EuclideanSpace ℝ (Fin (n+1))) volume volume :=
    PiLp.volume_preserving_toLp _
  have : unsplit n = (WithLp.toLp 2 : (Fin (n+1) → ℝ) → EuclideanSpace ℝ (Fin (n+1)))
      ∘ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm)
      ∘ (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))) := by
    funext p; rfl
  rw [this]
  exact h3.comp (h2.comp h1)

lemma unsplit_norm (n : ℕ) (x : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖unsplit n (x, v)‖^2 = x^2 + ‖v‖^2 := by
  rw [norm_sq_eq, norm_sq_eq, Fin.sum_univ_succ, unsplit_zero]
  congr 1

lemma unsplit_shift (n : ℕ) (x y : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    unsplit n (y, v) = unsplit n (x, v) + (y - x) • EuclideanSpace.single (0 : Fin (n+1)) (1:ℝ) := by
  classical
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [unsplit_zero]
  · intro j
    simp [unsplit_succ, EuclideanSpace.single, Fin.succ_ne_zero]

/-- A set of reals of diameter at most `W` has measure at most `W`. -/
lemma vol_diam (s : Set ℝ) (W : ℝ) (hW : 0 ≤ W)
    (h : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ W) : volume s ≤ ENNReal.ofReal W := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  · have hbdd : BddBelow s := ⟨x₀ - W, fun z hz => by
      have := h x₀ hx₀ z hz
      cases abs_le.mp this with | intro l r => linarith⟩
    have hsub : s ⊆ Set.Icc (sInf s) (sInf s + W) := by
      intro y hy
      refine ⟨csInf_le hbdd hy, ?_⟩
      have hlb : y - W ≤ sInf s := le_csInf ⟨x₀, hx₀⟩ (fun z hz => by
        have := h y hy z hz
        cases abs_le.mp this with | intro l r => linarith)
      linarith
    calc volume s ≤ volume (Set.Icc (sInf s) (sInf s + W)) := measure_mono hsub
      _ = ENNReal.ofReal W := by rw [Real.volume_Icc]; congr 1; ring

/-- Fubini slab bound in the standard frame. -/
lemma slab_e0 (n : ℕ) (hn : 1 ≤ n) (E : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hE : MeasurableSet E) (ρ W : ℝ) (hρ : 0 ≤ ρ) (hW : 0 ≤ W)
    (h1 : ∀ u ∈ E, ‖u‖ ≤ ρ)
    (h2 : ∀ (x y : ℝ) (v : EuclideanSpace ℝ (Fin n)),
       unsplit n (x,v) ∈ E → unsplit n (y,v) ∈ E → |x - y| ≤ W) :
    volume E ≤ ENNReal.ofReal (W * (ρ^n * vv n)) := by
  classical
  have hFm : MeasurableSet ((unsplit n) ⁻¹' E) := hE.preimage (unsplit_mp n).measurable
  have hvolF : volume ((unsplit n) ⁻¹' E) = volume E :=
    (unsplit_mp n).measure_preimage hE.nullMeasurableSet
  have hprod : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n)))
      = (volume : Measure ℝ).prod volume := rfl
  have hfib : ∀ v : EuclideanSpace ℝ (Fin n),
      volume ((fun x => (x, v)) ⁻¹' ((unsplit n) ⁻¹' E))
        ≤ (closedBall (0:EuclideanSpace ℝ (Fin n)) ρ).indicator
            (fun _ => ENNReal.ofReal W) v := by
    intro v
    by_cases hv : ‖v‖ ≤ ρ
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hv)]
      refine vol_diam _ _ hW ?_
      intro x hx y hy
      exact h2 x y v hx hy
    · have hempty : (fun x => (x, v)) ⁻¹' ((unsplit n) ⁻¹' E) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hmem
        have hb := h1 _ hmem
        have hn2 := unsplit_norm n x v
        exact hv (by nlinarith [norm_nonneg v, norm_nonneg (unsplit n (x,v)), sq_nonneg x])
      rw [hempty]; simp
  rw [← hvolF, hprod, Measure.prod_apply_symm hFm]
  calc ∫⁻ v, volume ((fun x => (x, v)) ⁻¹' ((unsplit n) ⁻¹' E)) ∂volume
      ≤ ∫⁻ v, (closedBall (0:EuclideanSpace ℝ (Fin n)) ρ).indicator
          (fun _ => ENNReal.ofReal W) v ∂volume := lintegral_mono hfib
    _ = ENNReal.ofReal W * volume (closedBall (0:EuclideanSpace ℝ (Fin n)) ρ) := by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
    _ = ENNReal.ofReal (W * (ρ^n * vv n)) := by
        rw [volume_cb n hn 0 ρ hρ, ← ENNReal.ofReal_mul hW]

/-- Slab bound in an arbitrary direction: a measurable set of diameter `≤ ρ` whose fibres in
the direction `e` have diameter `≤ W` has volume at most `W ρ^n v_n`. -/
lemma slab_gen (n : ℕ) (hn : 1 ≤ n) (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖ = 1)
    (E : Set (EuclideanSpace ℝ (Fin (n+1)))) (hE : MeasurableSet E) (ρ W : ℝ)
    (hρ : 0 ≤ ρ) (hW : 0 ≤ W)
    (h1 : ∀ u ∈ E, ‖u‖ ≤ ρ)
    (h2 : ∀ u ∈ E, ∀ c : ℝ, u + c • e ∈ E → |c| ≤ W) :
    volume E ≤ ENNReal.ofReal (W * (ρ^n * vv n)) := by
  classical
  have horth : Orthonormal ℝ (({0} : Set (Fin (n+1))).domRestrict (fun _ : Fin (n+1) => e)) := by
    constructor
    · intro i; simpa [Set.domRestrict] using he
    · intro i j hij
      exact absurd (Subtype.ext (by rw [i.2, j.2] : (i : Fin (n+1)) = j)) hij
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = e := hb 0 rfl
  have hsymm : b.repr.symm (EuclideanSpace.single (0 : Fin (n+1)) (1:ℝ)) = e := by
    rw [← hb0, ← b.repr_self 0]; simp
  set E' : Set (EuclideanSpace ℝ (Fin (n+1))) := (b.repr.symm) ⁻¹' E with hE'
  have hE'm : MeasurableSet E' := hE.preimage b.repr.symm.continuous.measurable
  have hvolE' : volume E' = volume E :=
    (b.measurePreserving_repr_symm).measure_preimage hE.nullMeasurableSet
  rw [← hvolE']
  refine slab_e0 n hn E' hE'm ρ W hρ hW ?_ ?_
  · intro u hu
    have := h1 _ hu
    rwa [b.repr.symm.norm_map] at this
  · intro x y v hx hy
    have hshift : unsplit n (y, v)
        = unsplit n (x, v) + (y - x) • EuclideanSpace.single (0 : Fin (n+1)) (1:ℝ) :=
      unsplit_shift n x y v
    have hmap : b.repr.symm (unsplit n (y, v))
        = b.repr.symm (unsplit n (x, v)) + (y - x) • e := by
      rw [hshift, map_add, map_smul, hsymm]
    have := h2 (b.repr.symm (unsplit n (x, v))) hx (y - x) (by rw [← hmap]; exact hy)
    rwa [abs_sub_comm] at this

set_option maxHeartbeats 1000000 in
/-- The intersection of a ball with a thin spherical shell has small volume: this is the
estimate that makes the shell configuration beat `2^d`. -/
lemma annulus_ball (n : ℕ) (hn : 1 ≤ n) (Y : EuclideanSpace ℝ (Fin (n+1)))
    (Rin Rout r : ℝ) (hr : 0 ≤ r) (hRin : 0 < Rin) (hRr : r^2 < Rin^2 - r^2)
    (hRio : Rin ≤ Rout) :
    volume {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u - Y‖ ≤ r ∧ Rin ≤ ‖u‖ ∧ ‖u‖ ≤ Rout}
      ≤ ENNReal.ofReal
          (((Rout^2 - Rin^2)/(2*Real.sqrt (Rin^2 - r^2))) * (r^n * vv n)) := by
  classical
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = (Rout^2 - Rin^2)/(2*Real.sqrt (Rin^2 - r^2)) := ⟨_, rfl⟩
  have hpos : 0 < Rin^2 - r^2 := by nlinarith [sq_nonneg r]
  have hsq : 0 < Real.sqrt (Rin^2 - r^2) := Real.sqrt_pos.mpr hpos
  have hsqsq : (Real.sqrt (Rin^2 - r^2))^2 = Rin^2 - r^2 := Real.sq_sqrt hpos.le
  have hRR : 0 ≤ Rout^2 - Rin^2 := by nlinarith [hRio, hr, hpos, hRin]
  have hW0 : 0 ≤ W := by rw [hWd]; positivity
  -- translate
  have htr : volume {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u - Y‖ ≤ r ∧ Rin ≤ ‖u‖ ∧ ‖u‖ ≤ Rout}
      = volume {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ r ∧ Rin ≤ ‖Y + u‖ ∧ ‖Y + u‖ ≤ Rout} := by
    have h : {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u‖ ≤ r ∧ Rin ≤ ‖Y + u‖ ∧ ‖Y + u‖ ≤ Rout}
        = (fun u => Y + u) ⁻¹'
          {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u - Y‖ ≤ r ∧ Rin ≤ ‖u‖ ∧ ‖u‖ ≤ Rout} := by
      ext u; simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by simpa using h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by simpa using h1, h2, h3⟩
    rw [h, measure_preimage_add]
  rw [htr, ← hWd]
  set E : Set (EuclideanSpace ℝ (Fin (n+1))) :=
    {u | ‖u‖ ≤ r ∧ Rin ≤ ‖Y + u‖ ∧ ‖Y + u‖ ≤ Rout} with hEdef
  have hEm : MeasurableSet E := by
    have c1 : Continuous (fun u : EuclideanSpace ℝ (Fin (n+1)) => ‖u‖) := continuous_norm
    have c2 : Continuous (fun u : EuclideanSpace ℝ (Fin (n+1)) => ‖Y + u‖) :=
      continuous_norm.comp (continuous_const.add continuous_id)
    exact ((isClosed_le c1 continuous_const).inter
      ((isClosed_le continuous_const c2).inter (isClosed_le c2 continuous_const))).measurableSet
  by_cases hY : Y = 0
  · have : E = ∅ := by
      ext u
      simp only [hEdef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hY, zero_add]
      rintro ⟨h1, h2, -⟩
      nlinarith [norm_nonneg u, hRr, hr, hRin]
    rw [this]; simp
  · have htpos : 0 < ‖Y‖ := norm_pos_iff.mpr hY
    obtain ⟨e, hedef⟩ : ∃ e, e = ‖Y‖⁻¹ • Y := ⟨_, rfl⟩
    have he : ‖e‖ = 1 := by
      rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt htpos)]
    have hYe : Y = ‖Y‖ • e := by rw [hedef, smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul]
    refine le_trans (slab_gen n hn e he E hEm r W hr hW0 (fun u hu => hu.1) ?_) (le_of_eq rfl)
    intro u hu c hc
    obtain ⟨hu1, hu2, hu3⟩ := hu
    obtain ⟨hc1, hc2, hc3⟩ := hc
    obtain ⟨t, htd⟩ : ∃ t : ℝ, t = ‖Y‖ := ⟨_, rfl⟩
    obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = inner ℝ e u := ⟨_, rfl⟩
    have hYu : inner ℝ Y u = t * s := by rw [hYe, real_inner_smul_left, ← htd, ← hsd]
    have hee : inner ℝ e e = (1:ℝ) := by
      rw [real_inner_self_eq_norm_mul_norm, he]; ring
    have hsabs : |s| ≤ r := by
      rw [hsd]
      calc |inner ℝ e u| ≤ ‖e‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * r := by rw [he]; exact mul_le_mul_of_nonneg_left hu1 zero_le_one
        _ = r := one_mul r
    have hsc : inner ℝ e (u + c • e) = s + c := by
      rw [inner_add_right, real_inner_smul_right, hee, ← hsd]; ring
    have hscabs : |s + c| ≤ r := by
      rw [← hsc]
      calc |inner ℝ e (u + c • e)| ≤ ‖e‖ * ‖u + c • e‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * r := by rw [he]; exact mul_le_mul_of_nonneg_left hc1 zero_le_one
        _ = r := one_mul r
    -- the two squared norms
    have hn1 : ‖Y + u‖^2 = (t + s)^2 + (‖u‖^2 - s^2) := by
      rw [norm_add_sq_real, hYu, ← htd]; ring
    have huc : ‖u + c • e‖^2 = ‖u‖^2 + 2*c*s + c^2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, he, mul_one,
        sq_abs, real_inner_comm e u, ← hsd]
      ring
    have hn2 : ‖Y + (u + c • e)‖^2 = (t + s + c)^2 + (‖u‖^2 - s^2) := by
      rw [norm_add_sq_real, inner_add_right, hYu, real_inner_smul_right, huc, ← htd]
      have hYe2 : inner ℝ Y e = t := by
        rw [hYe, real_inner_smul_left, hee, ← htd]; ring
      rw [hYe2]; ring
    -- positivity of the two radial coordinates
    have hsu : |s| ≤ ‖u‖ := by
      rw [hsd]
      calc |inner ℝ e u| ≤ ‖e‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ = ‖u‖ := by rw [he]; ring
    have hw : 0 ≤ ‖u‖^2 - s^2 := by
      have h : s^2 ≤ ‖u‖^2 := by
        rw [← sq_abs s]; exact pow_le_pow_left₀ (abs_nonneg s) hsu 2
      linarith
    have hwr : ‖u‖^2 - s^2 ≤ r^2 := by
      have h : ‖u‖^2 ≤ r^2 := pow_le_pow_left₀ (norm_nonneg u) hu1 2
      linarith [sq_nonneg s]
    have hA2 : Rin^2 - r^2 ≤ (t+s)^2 := by
      have h1 : Rin^2 ≤ ‖Y + u‖^2 := pow_le_pow_left₀ hRin.le hu2 2
      rw [hn1] at h1; linarith [hwr]
    have hB2 : Rin^2 - r^2 ≤ (t+s+c)^2 := by
      have h1 : Rin^2 ≤ ‖Y + (u + c • e)‖^2 := pow_le_pow_left₀ hRin.le hc2 2
      rw [hn2] at h1; linarith [hwr]
    have ht0 : 0 ≤ t := by rw [htd]; exact norm_nonneg Y
    have hApos : 0 < t + s := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hsl, hsr⟩ := abs_le.mp hsabs
      nlinarith [hA2, hRr, mul_nonneg (by linarith : (0:ℝ) ≤ t + s + r)
        (by linarith : (0:ℝ) ≤ -(t + s))]
    have hBpos : 0 < t + s + c := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hsl, hsr⟩ := abs_le.mp hscabs
      nlinarith [hB2, hRr, mul_nonneg (by linarith : (0:ℝ) ≤ t + s + c + r)
        (by linarith : (0:ℝ) ≤ -(t + s + c))]
    have hAge : Real.sqrt (Rin^2 - r^2) ≤ t + s := by
      have h := Real.sqrt_le_sqrt hA2
      rwa [Real.sqrt_sq hApos.le] at h
    have hBge : Real.sqrt (Rin^2 - r^2) ≤ t + s + c := by
      have h := Real.sqrt_le_sqrt hB2
      rwa [Real.sqrt_sq hBpos.le] at h
    -- the difference of squares
    have hdiff : |c| * ((t+s) + (t+s+c)) ≤ Rout^2 - Rin^2 := by
      have hup : (t+s+c)^2 - (t+s)^2 ≤ Rout^2 - Rin^2 := by
        nlinarith [hc3, hu2, hn1, hn2, norm_nonneg (Y + u), norm_nonneg (Y + (u + c • e))]
      have hlo : (t+s)^2 - (t+s+c)^2 ≤ Rout^2 - Rin^2 := by
        nlinarith [hu3, hc2, hn1, hn2, norm_nonneg (Y + u), norm_nonneg (Y + (u + c • e))]
      rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc'] <;> nlinarith
    rw [hWd, le_div_iff₀ (by positivity)]
    nlinarith [hdiff, hAge, hBge, abs_nonneg c, hsq]

lemma count_upper' (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (U : Finset (Fin d → ℤ))
    (hU : ∀ z ∈ U, cube d z ⊆ S) :
    (U.card : ℝ≥0∞) ≤ volume S := by
  have hsub : (⋃ z ∈ U, cube d z) ⊆ S := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, hz, hxz⟩ := hx
    exact hU z hz hxz
  have heq : volume (⋃ z ∈ U, cube d z) = (U.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset (cube_pd d U) (fun z _ => cube_meas d z)]
    simp [cube_vol]
  rw [← heq]
  exact measure_mono hsub

/-- `(1+x)^n ≤ 1/(1-n x)` for `0 ≤ x` and `n x < 1`. -/
lemma one_add_pow_le : ∀ (n : ℕ) (x : ℝ), 0 ≤ x → (n:ℝ)*x < 1 → (1+x)^n ≤ 1/(1-(n:ℝ)*x)
  | 0, x, _, _ => by norm_num
  | (n+1), x, hx, h => by
      have hnx : (n:ℝ)*x < 1 := by push_cast at h; nlinarith
      have hd1 : (0:ℝ) < 1 - (n:ℝ)*x := by linarith
      have hd2 : (0:ℝ) < 1 - ((n:ℝ)+1)*x := by push_cast at h; linarith
      have hIH := one_add_pow_le n x hx hnx
      have hstep : (1+x) * (1/(1-(n:ℝ)*x)) ≤ 1/(1-((n:ℝ)+1)*x) := by
        rw [mul_one_div, div_le_div_iff₀ hd1 hd2]
        nlinarith [sq_nonneg x, hx, Nat.cast_nonneg (α := ℝ) n]
      calc (1+x)^(n+1) = (1+x) * (1+x)^n := by ring
        _ ≤ (1+x) * (1/(1-(n:ℝ)*x)) := by
            exact mul_le_mul_of_nonneg_left hIH (by linarith)
        _ ≤ 1/(1-((n:ℝ)+1)*x) := hstep
        _ = 1/(1-((n+1:ℕ):ℝ)*x) := by push_cast; ring_nf

/-- `a^d - b^d ≥ d b^(d-1) (a-b)` for `0 ≤ b ≤ a`. -/
lemma pow_sub_pow_ge : ∀ (d : ℕ) (a b : ℝ), 0 ≤ b → b ≤ a →
    (d:ℝ) * b^d * (a - b) ≤ b * (a^d - b^d)
  | 0, a, b, _, _ => by simp
  | (d+1), a, b, hb, hab => by
      have hIH := pow_sub_pow_ge d a b hb hab
      have ha : 0 ≤ a := le_trans hb hab
      have hbd : (0:ℝ) ≤ b^d := pow_nonneg hb d
      have hab0 : (0:ℝ) ≤ a - b := by linarith
      have h1 : a * ((d:ℝ) * b^d * (a-b)) ≤ a * (b * (a^d - b^d)) :=
        mul_le_mul_of_nonneg_left hIH ha
      have h2 : (d:ℝ) * b^(d+1) * (a-b) ≤ a * ((d:ℝ) * b^d * (a-b)) := by
        have he : (d:ℝ) * b^(d+1) * (a-b) = b * ((d:ℝ) * b^d * (a-b)) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_right hab (by positivity)
      have hgoal : b * (a^(d+1) - b^(d+1)) = a * (b * (a^d - b^d)) + b^(d+1)*(a-b) := by ring
      push_cast
      rw [hgoal]
      nlinarith [h1, h2, hbd, hab0]

lemma transport4 {ι : Type} [Fintype ι] (d : ℕ) (p : ι → EuclideanSpace ℝ (Fin d)) (k : ℕ)
    (h1 : ∀ i, ‖p i‖ ≤ 2)
    (h2 : ∀ y : EuclideanSpace ℝ (Fin d), {i : ι | dist y (p i) ≤ 1}.ncard ≤ k)
    (h3 : 2^d * k < Fintype.card ι) :
    ∃ (m k' : ℕ) (p' : Fin m → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖p' i‖ ≤ 2) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), {i : Fin m | dist y (p' i) ≤ 1}.ncard ≤ k') ∧
      2^d * k' < m := by
  classical
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, k, fun j => p (e.symm j), fun j => h1 _, ?_, h3⟩
  intro y
  rw [ncard_equiv e (fun i => dist y (p i) ≤ 1)]
  exact h2 y

set_option maxHeartbeats 1000000 in
/-- The pure real-arithmetic core of the shell construction. -/
lemma shell_numeric (n : ℕ) (aa hh Nr : ℝ)
    (haa0 : 0 ≤ aa) (hh0 : 0 < hh) (hhle : hh ≤ 1/200) (hNr : 1 ≤ Nr)
    (hdRhh : ((n:ℝ)+1)*hh = 1/100)
    (haa1 : aa*40000 ≤ Nr) (haa2 : (n:ℝ)*aa*20000 ≤ Nr) (haa200 : 200*aa ≤ hh*Nr) :
    ((2*Nr + aa)^2 - (Nr*(2-hh) - aa)^2)
        /(2*Real.sqrt ((Nr*(2-hh) - aa)^2 - (Nr + aa)^2)) ≤ (6/5)*hh*Nr
    ∧ (Nr + aa)^n ≤ (101/100)*Nr^n
    ∧ (49/50)*((n:ℝ)+1)*2^n*hh*Nr^(n+1)
        ≤ (2*Nr - aa)^(n+1) - (Nr*(2-hh) + aa)^(n+1) := by
  have hN0 : (0:ℝ) < Nr := by linarith
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · -- the fibre width
    have hnum : (2*Nr + aa)^2 - (Nr*(2-hh) - aa)^2 ≤ (101/25)*hh*Nr^2 := by
      nlinarith [haa200, hh0, hNr, haa0, hhle]
    have hsqin : ((1723/1000)*Nr)^2 ≤ (Nr*(2-hh) - aa)^2 - (Nr + aa)^2 := by
      nlinarith [haa1, hh0, hNr, haa0, hhle]
    have hsqrtlo : (1723/1000)*Nr ≤ Real.sqrt ((Nr*(2-hh) - aa)^2 - (Nr + aa)^2) := by
      have h := Real.sqrt_le_sqrt hsqin
      rwa [Real.sqrt_sq (by positivity)] at h
    have hdenpos : (0:ℝ) < 2*Real.sqrt ((Nr*(2-hh) - aa)^2 - (Nr + aa)^2) := by linarith
    have hc : (0:ℝ) ≤ (6/5)*hh*Nr := by nlinarith
    rw [div_le_iff₀ hdenpos]
    calc (2*Nr + aa)^2 - (Nr*(2-hh) - aa)^2 ≤ (101/25)*hh*Nr^2 := hnum
      _ ≤ (6/5)*hh*Nr * (2*((1723/1000)*Nr)) := by nlinarith [mul_nonneg hh0.le (sq_nonneg Nr)]
      _ ≤ (6/5)*hh*Nr * (2*Real.sqrt ((Nr*(2-hh) - aa)^2 - (Nr + aa)^2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
  · -- the transverse radius
    have hx : (0:ℝ) ≤ aa/Nr := by positivity
    have hnx : (n:ℝ)*(aa/Nr) ≤ 1/20000 := by
      rw [← mul_div_assoc, div_le_iff₀ hN0]; linarith
    have hpow := one_add_pow_le n (aa/Nr) hx (by linarith)
    have hfac : Nr + aa = Nr * (1 + aa/Nr) := by field_simp
    have hb : (1 + aa/Nr)^n ≤ 101/100 := by
      refine le_trans hpow ?_
      rw [div_le_iff₀ (by linarith)]; linarith
    rw [hfac, mul_pow]
    nlinarith [hb, pow_nonneg hN0.le n]
  · -- the shell mass
    have hR1pos : (0:ℝ) < Nr*(2-hh) + aa := by nlinarith
    have hR10 : (0:ℝ) ≤ Nr*(2-hh) + aa := hR1pos.le
    have hR1R2 : Nr*(2-hh) + aa ≤ 2*Nr - aa := by nlinarith [haa200, hh0]
    have hR2R1 : (99/100)*Nr*hh ≤ (2*Nr - aa) - (Nr*(2-hh) + aa) := by nlinarith [haa200]
    have hR0pow : 2^n*(199/200) ≤ (2-hh)^n := by
      have hb := one_add_mul_le_pow (a := -(hh/2)) (by linarith) n
      rw [show (1:ℝ) + -(hh/2) = 1 - hh/2 by ring] at hb
      have hnhh : (n:ℝ)*(hh/2) ≤ 1/200 := by nlinarith [hdRhh, hh0]
      have hfac2 : (2:ℝ)-hh = 2*(1 - hh/2) := by ring
      rw [hfac2, mul_pow]
      nlinarith [hb, hnhh, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
    have hR1lo : 2^n*(199/200)*Nr^n ≤ (Nr*(2-hh) + aa)^n := by
      have h1 : Nr*(2-hh) ≤ Nr*(2-hh) + aa := by linarith
      have h2 : (Nr*(2-hh))^n ≤ (Nr*(2-hh) + aa)^n :=
        pow_le_pow_left₀ (by nlinarith) h1 n
      rw [mul_pow] at h2
      nlinarith [h2, hR0pow, pow_nonneg hN0.le n]
    have hps := pow_sub_pow_ge (n+1) (2*Nr - aa) (Nr*(2-hh) + aa) hR10 hR1R2
    push_cast at hps
    have hid : ((n:ℝ)+1)*(Nr*(2-hh) + aa)^(n+1)*((2*Nr - aa) - (Nr*(2-hh) + aa))
        = (Nr*(2-hh) + aa) * (((n:ℝ)+1)*(Nr*(2-hh) + aa)^n
            *((2*Nr - aa) - (Nr*(2-hh) + aa))) := by ring
    rw [hid] at hps
    have hdiv : ((n:ℝ)+1)*(Nr*(2-hh) + aa)^n*((2*Nr - aa) - (Nr*(2-hh) + aa))
        ≤ (2*Nr - aa)^(n+1) - (Nr*(2-hh) + aa)^(n+1) :=
      le_of_mul_le_mul_left hps hR1pos
    refine le_trans ?_ hdiv
    have step1 : 2^n*(199/200)*Nr^n * ((99/100)*Nr*hh)
        ≤ (Nr*(2-hh) + aa)^n * ((2*Nr - aa) - (Nr*(2-hh) + aa)) :=
      mul_le_mul hR1lo hR2R1 (by positivity) (pow_nonneg hR10 n)
    have step2 : ((n:ℝ)+1) * (2^n*(199/200)*Nr^n * ((99/100)*Nr*hh))
        ≤ ((n:ℝ)+1) * ((Nr*(2-hh) + aa)^n * ((2*Nr - aa) - (Nr*(2-hh) + aa))) :=
      mul_le_mul_of_nonneg_left step1 (by linarith)
    have hNp : Nr^(n+1) = Nr^n * Nr := by ring
    rw [hNp]
    have hmono : (0:ℝ) ≤ ((n:ℝ)+1)*2^n*hh*(Nr^n*Nr) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hh0.le)
        (mul_nonneg (pow_nonneg hN0.le n) hN0.le)
    linarith [step2, hmono]

set_option maxHeartbeats 1000000 in
/-- The volume comparison that makes the shell beat `2^d`. -/
lemma vv_compare (n : ℕ) (hn : 1 ≤ n) :
    (303/125:ℝ)*vv n < (97/100)*((n:ℝ)+1)*vv (n+1) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hv := vv_step2 n
  have hsp : (0:ℝ) < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hkey : (303/125:ℝ) * Real.sqrt ((n:ℝ)+2)
      < (97/100)*((n:ℝ)+1)*Real.sqrt (2*Real.pi) := by
    have hL : (0:ℝ) ≤ (303/125:ℝ) * Real.sqrt ((n:ℝ)+2) := by positivity
    have hR : (0:ℝ) ≤ (97/100)*((n:ℝ)+1)*Real.sqrt (2*Real.pi) := by positivity
    have hs1 : ((303/125:ℝ) * Real.sqrt ((n:ℝ)+2))^2 = (91809/15625)*((n:ℝ)+2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    have hs2 : ((97/100:ℝ)*((n:ℝ)+1)*Real.sqrt (2*Real.pi))^2
        = (9409/10000)*((n:ℝ)+1)^2*(2*Real.pi) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hlt2 : ((303/125:ℝ) * Real.sqrt ((n:ℝ)+2))^2
        < ((97/100:ℝ)*((n:ℝ)+1)*Real.sqrt (2*Real.pi))^2 := by
      rw [hs1, hs2]
      nlinarith [Real.pi_gt_three, hnR,
        mul_pos (by nlinarith : (0:ℝ) < ((n:ℝ)+1)^2)
          (by linarith [Real.pi_gt_three] : (0:ℝ) < Real.pi - 3)]
    nlinarith [hlt2, hL, hR]
  have h1 : (303/125:ℝ)*(vv n * Real.sqrt (2*Real.pi))
      ≤ (303/125)*(Real.sqrt ((n:ℝ)+2) * vv (n+1)) :=
    mul_le_mul_of_nonneg_left hv (by norm_num)
  have h2 := mul_lt_mul_of_pos_right hkey (vv_pos (n+1))
  have h3 : (303/125:ℝ)*vv n * Real.sqrt (2*Real.pi)
      < ((97/100)*((n:ℝ)+1)*vv (n+1)) * Real.sqrt (2*Real.pi) := by nlinarith [h1, h2]
  exact lt_of_mul_lt_mul_right h3 (Real.sqrt_nonneg _)

set_option maxHeartbeats 1000000 in
/-- Putting the four numeric bounds together. -/
lemma shell_final (n : ℕ) (hn : 1 ≤ n) (hh Nr W rrn kk R1p R2p : ℝ)
    (hh0 : 0 < hh) (hNr : 1 ≤ Nr) (hW0 : 0 ≤ W) (hrrn0 : 0 ≤ rrn)
    (hB1 : W ≤ (6/5)*hh*Nr) (hB2 : rrn ≤ (101/100)*Nr^n)
    (hB3 : (49/50)*((n:ℝ)+1)*2^n*hh*Nr^(n+1) ≤ R2p - R1p)
    (hB4 : (2:ℝ)^(n+1) ≤ 2^n*hh*Nr^(n+1)*((1/100)*((n:ℝ)+1)*vv (n+1)))
    (hkb : kk < W*(rrn*vv n) + 1) :
    (2:ℝ)^(n+1)*kk < (R2p - R1p)*vv (n+1) := by
  have hN0 : (0:ℝ) < Nr := by linarith
  have hvvn0 : (0:ℝ) ≤ vv n := (vv_pos n).le
  have hnum := vv_compare n hn
  have hposn : (0:ℝ) < 2^n*hh*Nr^(n+1) :=
    mul_pos (mul_pos (by positivity) hh0) (by positivity)
  have hstepB : (2:ℝ)^(n+1)*(W*(rrn*vv n)) ≤ 2^n*hh*Nr^(n+1)*((303/125)*vv n) := by
    have h1 : W*(rrn*vv n) ≤ ((6/5)*hh*Nr)*(((101/100)*Nr^n)*vv n) := by
      refine mul_le_mul hB1 (mul_le_mul_of_nonneg_right hB2 hvvn0)
        (mul_nonneg hrrn0 hvvn0) ?_
      nlinarith [hh0, hNr]
    have h2 : (2:ℝ)^(n+1)*(W*(rrn*vv n))
        ≤ 2^(n+1)*(((6/5)*hh*Nr)*(((101/100)*Nr^n)*vv n)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2:ℝ)^(n+1)*(((6/5)*hh*Nr)*(((101/100)*Nr^n)*vv n))
        = 2^n*hh*Nr^(n+1)*((303/125)*vv n) := by
      rw [show (2:ℝ)^(n+1) = 2*2^n by ring, show Nr^(n+1) = Nr^n*Nr by ring]
      ring
    linarith [h2, h3]
  have hstepD : 2^n*hh*Nr^(n+1)*((303/125)*vv n) + 2^n*hh*Nr^(n+1)*((1/100)*((n:ℝ)+1)*vv (n+1))
      < 2^n*hh*Nr^(n+1)*((49/50)*((n:ℝ)+1)*vv (n+1)) := by
    nlinarith [hnum, hposn]
  have hstepE : 2^n*hh*Nr^(n+1)*((49/50)*((n:ℝ)+1)*vv (n+1)) ≤ (R2p - R1p)*vv (n+1) := by
    have h := mul_le_mul_of_nonneg_right hB3 (vv_pos (n+1)).le
    nlinarith [h]
  have hp : (0:ℝ) < 2^(n+1) := by positivity
  nlinarith [hkb, hstepB, hB4, hstepD, hstepE, hp]

set_option maxHeartbeats 1000000 in
theorem shell_barrier (d : ℕ) (hd : 2 ≤ d) :
    ∃ (m k : ℕ) (p : Fin m → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖p i‖ ≤ 2) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), {i : Fin m | dist y (p i) ≤ 1}.ncard ≤ k) ∧
      2 ^ d * k < m := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨dR, hdR⟩ : ∃ dR : ℝ, dR = ((n:ℝ)+1) := ⟨_, rfl⟩
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hdR2 : (2:ℝ) ≤ dR := by rw [hdR]; linarith
  obtain ⟨aa, haad⟩ : ∃ aa : ℝ, aa = Real.sqrt dR / 2 := ⟨_, rfl⟩
  have haa0 : 0 ≤ aa := by rw [haad]; positivity
  obtain ⟨hh, hhd⟩ : ∃ hh : ℝ, hh = 1/(100*dR) := ⟨_, rfl⟩
  have hh0 : 0 < hh := by rw [hhd]; positivity
  have hhle : hh ≤ 1/200 := by
    rw [hhd]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  obtain ⟨R0, hR0d⟩ : ∃ R0 : ℝ, R0 = 2 - hh := ⟨_, rfl⟩
  have hR0lo : (399:ℝ)/200 ≤ R0 := by rw [hR0d]; linarith
  have hR0hi : R0 < 2 := by rw [hR0d]; linarith
  -- the scale
  have hvvp : 0 < vv (n+1) := vv_pos (n+1)
  have hden : (0:ℝ) < (1/100)*dR*(vv (n+1))*hh :=
    mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) hvvp) hh0
  obtain ⟨N, hN1, hN2, hN3⟩ : ∃ N : ℕ, 1 ≤ N ∧ 100*dR*aa ≤ hh*N ∧
      2 ≤ (1/100)*dR*(vv (n+1))*hh*(N:ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (max ((100*dR*aa)/hh) (2/((1/100)*dR*(vv (n+1))*hh))))
    have hb1 : (1:ℝ) ≤ N := le_trans (le_max_left _ _) hN
    refine ⟨N, by exact_mod_cast hb1, ?_, ?_⟩
    · have h := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
      rw [div_le_iff₀ hh0] at h; linarith
    · have h := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
      rw [div_le_iff₀ hden] at h; linarith
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  -- smallness of the lattice rounding radius
  have haa1 : aa*40000 ≤ (N:ℝ) := by nlinarith [hN2, hdR2, hhle, haa0, hh0, hNR]
  have haa2 : (n:ℝ)*aa*20000 ≤ (N:ℝ) := by
    have hnd : (n:ℝ) ≤ dR := by rw [hdR]; linarith
    nlinarith [hN2, hdR2, hhle, haa0, hh0, hNR, hnd]
  have haahh : aa ≤ hh*(N:ℝ) := by nlinarith [hN2, hdR2, haa0, hh0, hNR]
  -- the radii
  obtain ⟨Rin, hRind⟩ : ∃ Rin : ℝ, Rin = (N:ℝ)*R0 - aa := ⟨_, rfl⟩
  obtain ⟨Rout, hRoutd⟩ : ∃ Rout : ℝ, Rout = 2*(N:ℝ) + aa := ⟨_, rfl⟩
  obtain ⟨rr, hrrd⟩ : ∃ rr : ℝ, rr = (N:ℝ) + aa := ⟨_, rfl⟩
  obtain ⟨R1, hR1d⟩ : ∃ R1 : ℝ, R1 = (N:ℝ)*R0 + aa := ⟨_, rfl⟩
  obtain ⟨R2, hR2d⟩ : ∃ R2 : ℝ, R2 = 2*(N:ℝ) - aa := ⟨_, rfl⟩
  have hrr0 : 0 ≤ rr := by rw [hrrd]; linarith
  have hrrhi : rr ≤ (101/100)*(N:ℝ) := by rw [hrrd]; linarith
  have hRinlo : (199/100)*(N:ℝ) ≤ Rin := by rw [hRind]; nlinarith [hR0lo, haa1, hNR]
  have hRinpos : 0 < Rin := by nlinarith [hRinlo, hNR]
  have hRio : Rin ≤ Rout := by rw [hRind, hRoutd]; nlinarith [hR0hi, haa0, hNR]
  have hRr : rr^2 < Rin^2 - rr^2 := by nlinarith [hRinlo, hrrhi, hNR, hrr0, hRinpos]
  have hR1R2 : R1 ≤ R2 := by
    rw [hR1d, hR2d, hR0d]
    nlinarith [haa2, haahh, hh0, hNR, haa0, hdR2, hN2]
  have hR10 : 0 ≤ R1 := by rw [hR1d]; nlinarith [hR0lo, haa0, hNR]
  -- the lattice shell
  obtain ⟨Tset, hTd⟩ : ∃ T : Set (Fin (n+1) → ℤ),
      T = {z | (N:ℝ)*R0 ≤ ‖emb (n+1) z‖ ∧ ‖emb (n+1) z‖ ≤ 2*(N:ℝ)} := ⟨_, rfl⟩
  have hTfin : Tset.Finite := by
    refine Set.Finite.subset
      (Set.Finite.pi (fun _ : Fin (n+1) => Set.finite_Icc (-⌈2*(N:ℝ)⌉) ⌈2*(N:ℝ)⌉)) ?_
    intro z hz i _
    rw [hTd] at hz
    have h1 : |((z i : ℤ) : ℝ)| ≤ 2*(N:ℝ) := by
      have h2 := abs_coord_le (n+1) (emb (n+1) z) i
      rw [emb_apply] at h2
      exact le_trans h2 hz.2
    obtain ⟨hl, hr⟩ := abs_le.mp h1
    constructor
    · have h3 : ((-⌈2*(N:ℝ)⌉ : ℤ) : ℝ) ≤ ((z i : ℤ) : ℝ) := by
        push_cast; linarith [Int.le_ceil (2*(N:ℝ))]
      exact_mod_cast h3
    · have h3 : ((z i : ℤ) : ℝ) ≤ ((⌈2*(N:ℝ)⌉ : ℤ) : ℝ) := le_trans hr (Int.le_ceil _)
      exact_mod_cast h3
  have hTmem : ∀ w : Fin (n+1) → ℤ, w ∈ Tset →
      (N:ℝ)*R0 ≤ ‖emb (n+1) w‖ ∧ ‖emb (n+1) w‖ ≤ 2*(N:ℝ) := by
    intro w hw; rw [hTd] at hw; exact hw
  haveI : Fintype ↥Tset := hTfin.fintype
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = (Rout^2 - Rin^2)/(2*Real.sqrt (Rin^2 - rr^2)) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWd]
    have h1 : 0 ≤ Rout^2 - Rin^2 := by nlinarith [hRio, hRinpos]
    have h2 : 0 < Real.sqrt (Rin^2 - rr^2) := Real.sqrt_pos.mpr (by nlinarith [hRr, sq_nonneg rr])
    positivity
  obtain ⟨k, hkd⟩ : ∃ k : ℕ, k = ⌈W * (rr^n * vv n)⌉₊ := ⟨_, rfl⟩
  have hvvn0 : (0:ℝ) ≤ vv n := (vv_pos n).le
  have hcast : (((n+1 : ℕ)):ℝ) = dR := by rw [hdR]; push_cast; ring
  have hR20 : (0:ℝ) ≤ R2 := le_trans hR10 hR1R2
  -- coverage bound
  have hcov : ∀ y : EuclideanSpace ℝ (Fin (n+1)),
      {z : ↥Tset | dist y ((N:ℝ)⁻¹ • emb (n+1) (z : Fin (n+1) → ℤ)) ≤ 1}.ncard ≤ k := by
    intro y
    have hEq : {z : ↥Tset | dist y ((N:ℝ)⁻¹ • emb (n+1) (z : Fin (n+1) → ℤ)) ≤ 1}.ncard
        = ((hTfin.toFinset).filter
            (fun z => dist y ((N:ℝ)⁻¹ • emb (n+1) z) ≤ 1)).card := by
      have himg : Subtype.val ''
          {z : ↥Tset | dist y ((N:ℝ)⁻¹ • emb (n+1) (z : Fin (n+1) → ℤ)) ≤ 1}
          = ↑((hTfin.toFinset).filter (fun z => dist y ((N:ℝ)⁻¹ • emb (n+1) z) ≤ 1)) := by
        ext w
        simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_filter,
          Set.Finite.mem_toFinset]
        constructor
        · rintro ⟨⟨w', hw'⟩, hp, rfl⟩; exact ⟨hw', hp⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨w, h1⟩, h2, rfl⟩
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
        Set.ncard_eq_toFinset_card _ (Finset.finite_toSet _)]
      simp
    rw [hEq]
    obtain ⟨Y, hYd⟩ : ∃ Y, Y = (N:ℝ) • y := ⟨_, rfl⟩
    have hsub : ∀ z ∈ (hTfin.toFinset).filter (fun z => dist y ((N:ℝ)⁻¹ • emb (n+1) z) ≤ 1),
        cube (n+1) z ⊆
        {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u - Y‖ ≤ rr ∧ Rin ≤ ‖u‖ ∧ ‖u‖ ≤ Rout} := by
      intro z hz x hx
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, hTd] at hz
      obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
      have hxz : ‖x - emb (n+1) z‖ ≤ aa := by rw [haad, ← hcast]; exact Qb_norm (n+1) hx
      have hxz' : ‖emb (n+1) z - x‖ ≤ aa := by rw [← norm_neg]; simpa using hxz
      have hzY : ‖emb (n+1) z - Y‖ ≤ (N:ℝ) := by
        have h1 : y - (N:ℝ)⁻¹ • emb (n+1) z = (N:ℝ)⁻¹ • (Y - emb (n+1) z) := by
          rw [hYd, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hN0), one_smul]
        have h2 : ‖y - (N:ℝ)⁻¹ • emb (n+1) z‖ ≤ 1 := by rw [← dist_eq_norm]; exact hz3
        rw [h1, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hN0, inv_mul_eq_div,
          div_le_one hN0] at h2
        rw [← norm_neg, neg_sub]; exact h2
      refine ⟨?_, ?_, ?_⟩
      · calc ‖x - Y‖ = ‖(x - emb (n+1) z) + (emb (n+1) z - Y)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖x - emb (n+1) z‖ + ‖emb (n+1) z - Y‖ := norm_add_le _ _
          _ ≤ aa + (N:ℝ) := add_le_add hxz hzY
          _ = rr := by rw [hrrd]; ring
      · have htri : ‖emb (n+1) z‖ ≤ ‖emb (n+1) z - x‖ + ‖x‖ := by
          calc ‖emb (n+1) z‖ = ‖(emb (n+1) z - x) + x‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        rw [hRind]; linarith
      · have htri : ‖x‖ ≤ ‖x - emb (n+1) z‖ + ‖emb (n+1) z‖ := by
          calc ‖x‖ = ‖(x - emb (n+1) z) + emb (n+1) z‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        rw [hRoutd]; linarith
    have hcount := count_upper' (n+1)
      {u : EuclideanSpace ℝ (Fin (n+1)) | ‖u - Y‖ ≤ rr ∧ Rin ≤ ‖u‖ ∧ ‖u‖ ≤ Rout} _ hsub
    have hvol := annulus_ball n hn1 Y Rin Rout rr hrr0 hRinpos hRr hRio
    have h4 : (((hTfin.toFinset).filter
        (fun z => dist y ((N:ℝ)⁻¹ • emb (n+1) z) ≤ 1)).card : ℝ≥0∞)
        ≤ ENNReal.ofReal (W * (rr^n * vv n)) := by
      rw [hWd]; exact le_trans hcount hvol
    have hnn : (0:ℝ) ≤ W * (rr^n * vv n) :=
      mul_nonneg hW0 (mul_nonneg (pow_nonneg hrr0 n) hvvn0)
    have h5 : ((((hTfin.toFinset).filter
        (fun z => dist y ((N:ℝ)⁻¹ • emb (n+1) z) ≤ 1)).card : ℕ) : ℝ)
        ≤ W * (rr^n * vv n) := by
      rw [← ENNReal.ofReal_natCast] at h4
      exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h4
    rw [hkd]
    exact_mod_cast le_trans h5 (Nat.le_ceil _)
  -- lower bound on the number of shell points
  have hmlow : R2^(n+1) * vv (n+1) ≤ ((hTfin.toFinset.card : ℕ) : ℝ) + R1^(n+1) * vv (n+1) := by
    have hcover : ∀ x ∈ {x : EuclideanSpace ℝ (Fin (n+1)) | R1 ≤ ‖x‖ ∧ ‖x‖ ≤ R2},
        ∃ z ∈ hTfin.toFinset, x ∈ cube (n+1) z := by
      rintro x ⟨hx1, hx2⟩
      obtain ⟨z, hz⟩ := cube_cover (n+1) x
      have hxz : ‖x - emb (n+1) z‖ ≤ aa := by rw [haad, ← hcast]; exact Qb_norm (n+1) hz
      have hxz' : ‖emb (n+1) z - x‖ ≤ aa := by rw [← norm_neg]; simpa using hxz
      refine ⟨z, ?_, hz⟩
      rw [Set.Finite.mem_toFinset, hTd]
      constructor
      · have htri : ‖x‖ ≤ ‖x - emb (n+1) z‖ + ‖emb (n+1) z‖ := by
          calc ‖x‖ = ‖(x - emb (n+1) z) + emb (n+1) z‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        rw [hR1d] at hx1; linarith
      · have htri : ‖emb (n+1) z‖ ≤ ‖emb (n+1) z - x‖ + ‖x‖ := by
          calc ‖emb (n+1) z‖ = ‖(emb (n+1) z - x) + x‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        rw [hR2d] at hx2; linarith
    have hlow := count_lower (n+1) {x : EuclideanSpace ℝ (Fin (n+1)) | R1 ≤ ‖x‖ ∧ ‖x‖ ≤ R2}
      hTfin.toFinset hcover
    have hcl : closedBall (0:EuclideanSpace ℝ (Fin (n+1))) R2
        ⊆ {x : EuclideanSpace ℝ (Fin (n+1)) | R1 ≤ ‖x‖ ∧ ‖x‖ ≤ R2} ∪ closedBall 0 R1 := by
      intro x hx
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      rcases le_total R1 ‖x‖ with h | h
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (by simpa [Metric.mem_closedBall, dist_zero_right] using h)
    have hstep : ENNReal.ofReal (R2^(n+1) * vv (n+1))
        ≤ ((hTfin.toFinset.card : ℕ) : ℝ≥0∞) + ENNReal.ofReal (R1^(n+1) * vv (n+1)) := by
      rw [← volume_cb (n+1) (by omega) 0 R2 hR20, ← volume_cb (n+1) (by omega) 0 R1 hR10]
      exact le_trans (measure_mono hcl) (le_trans (measure_union_le _ _)
        (add_le_add hlow le_rfl))
    have hnn1 : (0:ℝ) ≤ R1^(n+1) * vv (n+1) :=
      mul_nonneg (pow_nonneg hR10 _) (vv_pos (n+1)).le
    rw [← ENNReal.ofReal_natCast (hTfin.toFinset.card), ← ENNReal.ofReal_add
      (Nat.cast_nonneg _) hnn1] at hstep
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hstep
  -- numeric preliminaries
  have haa200 : 200*aa ≤ hh*(N:ℝ) := by
    nlinarith [hN2, mul_nonneg haa0 (by linarith : (0:ℝ) ≤ dR - 2)]
  have hdRhh : ((n:ℝ)+1)*hh = 1/100 := by rw [hhd, ← hdR]; field_simp
  have hcardT : Fintype.card ↥Tset = hTfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card Tset hTfin, Set.ncard_eq_toFinset_card' Tset,
      Set.toFinset_card]
  rw [hR0d] at hRind hR1d
  obtain ⟨hB1', hB2', hB3'⟩ :=
    shell_numeric n aa hh (N:ℝ) haa0 hh0 hhle hNR hdRhh haa1 haa2 haa200
  have hB1 : W ≤ (6/5)*hh*(N:ℝ) := by rw [hWd, hRoutd, hRind, hrrd]; exact hB1'
  have hB2 : rr^n ≤ (101/100)*(N:ℝ)^n := by rw [hrrd]; exact hB2'
  have hB3 : (49/50)*((n:ℝ)+1)*2^n*hh*(N:ℝ)^(n+1) ≤ R2^(n+1) - R1^(n+1) := by
    rw [hR2d, hR1d]; exact hB3'
  have hB4 : (2:ℝ)^(n+1) ≤ 2^n*hh*(N:ℝ)^(n+1)*((1/100)*((n:ℝ)+1)*vv (n+1)) := by
    have hNn : (N:ℝ) ≤ (N:ℝ)^(n+1) := by
      calc (N:ℝ) = (N:ℝ)^1 := (pow_one _).symm
        _ ≤ (N:ℝ)^(n+1) := pow_le_pow_right₀ hNR (by omega)
    have h2 : (2:ℝ) ≤ (1/100)*dR*vv (n+1)*hh*(N:ℝ)^(n+1) :=
      le_trans hN3 (mul_le_mul_of_nonneg_left hNn (le_of_lt hden))
    rw [← hdR]
    have h3 : (2:ℝ)^n*2 ≤ 2^n*((1/100)*dR*vv (n+1)*hh*(N:ℝ)^(n+1)) :=
      mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num) n)
    have hexp : (2:ℝ)^(n+1) = 2^n*2 := by ring
    rw [hexp]
    linarith [h3]
  have hkb : (k:ℝ) < W*(rr^n*vv n) + 1 := by
    rw [hkd]
    exact Nat.ceil_lt_add_one (mul_nonneg hW0 (mul_nonneg (pow_nonneg hrr0 n) hvvn0))
  have hlt : (2:ℝ)^(n+1)*(k:ℝ) < (R2^(n+1) - R1^(n+1))*vv (n+1) :=
    shell_final n hn1 hh (N:ℝ) W (rr^n) (k:ℝ) (R1^(n+1)) (R2^(n+1)) hh0 hNR hW0
      (pow_nonneg hrr0 n) hB1 hB2 hB3 hB4 hkb
  have hcardlt : 2^(n+1)*k < Fintype.card ↥Tset := by
    have hexp : (R2^(n+1) - R1^(n+1))*vv (n+1)
        = R2^(n+1)*vv (n+1) - R1^(n+1)*vv (n+1) := by ring
    rw [hexp] at hlt
    have h1 : ((2^(n+1)*k : ℕ) : ℝ) < ((hTfin.toFinset.card : ℕ) : ℝ) := by
      push_cast
      linarith [hlt, hmlow]
    rw [hcardT]
    exact_mod_cast h1
  refine transport4 (n+1) (fun z : ↥Tset => (N:ℝ)⁻¹ • emb (n+1) (z : Fin (n+1) → ℤ)) k ?_
    hcov hcardlt
  intro z
  have hz := hTmem _ z.2
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hN0, inv_mul_eq_div, div_le_iff₀ hN0]
  linarith [hz.2]

/-- The submission: `Statements.PlyShellBarrier.statement`. -/
theorem proof :
    ∀ d : ℕ, 2 ≤ d →
      ∃ (m k : ℕ) (p : Fin m → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖p i‖ ≤ 2) ∧
        (∀ y : EuclideanSpace ℝ (Fin d), {i : Fin m | dist y (p i) ≤ 1}.ncard ≤ k) ∧
        2 ^ d * k < m :=
  fun d hd => shell_barrier d hd

end Submissions.PlyShellBarrier.AnnulusShell
