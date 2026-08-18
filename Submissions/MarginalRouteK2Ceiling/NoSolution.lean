import Mathlib

open MeasureTheory Set Function Classical

namespace Submissions.MarginalRouteK2Ceiling.NoSolution

noncomputable section

def T : Set (ℝ × ℝ) := {z | 0 ≤ z.1} ∩ {z | 0 ≤ z.2} ∩ {z | z.1 + z.2 ≤ 2}

lemma measurableSet_T : MeasurableSet T := by
  have h1 : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1} := measurableSet_le measurable_const measurable_fst
  have h2 : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.2} := measurableSet_le measurable_const measurable_snd
  have h3 : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ≤ 2} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  exact (h1.inter h2).inter h3

lemma mem_T {t₁ t₂ : ℝ} : (t₁, t₂) ∈ T ↔ (0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- Cauchy–Schwarz against the constant `1` on a finite-measure set, by completing a square. -/
theorem cs_set {s : Set ℝ} (hfin : volume s ≠ ⊤) (f : ℝ → ℝ)
    (h1 : IntegrableOn f s) (h2 : IntegrableOn (fun x => f x ^ 2) s) :
    (∫ x in s, f x) ^ 2 ≤ (volume s).toReal * ∫ x in s, f x ^ 2 := by
  set m := (volume s).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hm0 with hz | hpos
  · have hs0 : volume s = 0 := by
      have h := hz.symm
      rwa [hm, ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at h
    have hr : (volume.restrict s) = 0 := by rw [Measure.restrict_eq_zero]; exact hs0
    simp [hr, ← hz]
  · set P := ∫ x in s, f x with hP
    set Q := ∫ x in s, f x ^ 2 with hQ
    set L := P / m with hL
    have hcst : IntegrableOn (fun _ : ℝ => L ^ 2) s := integrableOn_const hfin (by simp)
    have hnn : 0 ≤ ∫ x in s, (f x - L) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have he : (fun x => (f x - L) ^ 2) = fun x => f x ^ 2 - 2 * L * f x + L ^ 2 := by
      funext x; ring
    have e1 : (∫ x in s, (f x ^ 2 - 2 * L * f x + L ^ 2))
        = (∫ x in s, (f x ^ 2 - 2 * L * f x)) + (∫ x in s, L ^ 2) :=
      integral_add (h2.sub (h1.const_mul (2 * L))) hcst
    have e2 : (∫ x in s, (f x ^ 2 - 2 * L * f x)) = Q - ∫ x in s, 2 * L * f x :=
      integral_sub h2 (h1.const_mul (2 * L))
    have e3 : (∫ x in s, 2 * L * f x) = 2 * L * P := integral_const_mul _ _
    have e4 : (∫ x in s, (L:ℝ) ^ 2) = m * L ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, hm, MeasureTheory.measureReal_def]
    rw [he, e1, e2, e3, e4] at hnn
    have hmne : m ≠ 0 := ne_of_gt hpos
    have hkey : P ^ 2 ≤ m * Q := by
      have hLdef : L = P / m := hL
      rw [hLdef] at hnn
      have hA : m * (P / m) ^ 2 = P ^ 2 / m := by field_simp
      rw [hA] at hnn
      have hB : 2 * (P / m) * P = 2 * P ^ 2 / m := by field_simp
      rw [hB] at hnn
      have : P ^ 2 / m ≤ Q := by
        have h2' : (2:ℝ) * P ^ 2 / m = 2 * (P ^ 2 / m) := by ring
        rw [h2'] at hnn
        linarith
      rw [div_le_iff₀ hpos] at this
      linarith
    linarith

/-- Fubini over the triangle, integrating `t₂` first. -/
lemma tri_int {f g : ℝ → ℝ} (hf0 : ∀ t, t < 0 → f t = 0)
    (hint : Integrable (uncurry fun t₁ t₂ => T.indicator (fun z => f z.1 * g z.2) (t₁, t₂))
      (volume.prod volume)) :
    ∫ z, T.indicator (fun z => f z.1 * g z.2) z ∂(volume.prod volume)
      = ∫ t₁, f t₁ * ∫ t₂ in Icc (0:ℝ) (2 - t₁), g t₂ := by
  rw [← integral_integral hint]
  congr 1
  funext t₁
  by_cases ht : (0:ℝ) ≤ t₁
  · have hind : ∀ t₂ : ℝ, T.indicator (fun z => f z.1 * g z.2) (t₁, t₂)
        = (Icc (0:ℝ) (2 - t₁)).indicator (fun t₂ => f t₁ * g t₂) t₂ := by
      intro t₂
      simp only [Set.indicator_apply, mem_T, Set.mem_Icc]
      by_cases h : (0:ℝ) ≤ t₂ ∧ t₂ ≤ 2 - t₁
      · rw [if_pos ⟨ht, h.1, by linarith [h.2]⟩, if_pos h]
      · rw [if_neg, if_neg h]
        rintro ⟨-, h2, h3⟩
        exact h ⟨h2, by linarith⟩
    simp_rw [hind]
    rw [integral_indicator measurableSet_Icc, integral_const_mul]
  · have hz : f t₁ = 0 := hf0 t₁ (lt_of_not_ge ht)
    have hind : ∀ t₂ : ℝ, T.indicator (fun z => f z.1 * g z.2) (t₁, t₂) = 0 := by
      intro t₂
      simp only [Set.indicator_apply, mem_T]
      rw [if_neg]
      rintro ⟨h1, -, -⟩
      exact ht h1
    simp_rw [hind]
    simp [hz]

/-- Fubini over the triangle, integrating `t₁` first. -/
lemma tri_int' {f g : ℝ → ℝ} (hg0 : ∀ t, t < 0 → g t = 0)
    (hint : Integrable (uncurry fun t₁ t₂ => T.indicator (fun z => f z.1 * g z.2) (t₁, t₂))
      (volume.prod volume)) :
    ∫ z, T.indicator (fun z => f z.1 * g z.2) z ∂(volume.prod volume)
      = ∫ t₂, g t₂ * ∫ t₁ in Icc (0:ℝ) (2 - t₂), f t₁ := by
  rw [← integral_integral hint, integral_integral_swap hint]
  congr 1
  funext t₂
  by_cases ht : (0:ℝ) ≤ t₂
  · have hind : ∀ t₁ : ℝ, T.indicator (fun z => f z.1 * g z.2) (t₁, t₂)
        = (Icc (0:ℝ) (2 - t₂)).indicator (fun t₁ => g t₂ * f t₁) t₁ := by
      intro t₁
      simp only [Set.indicator_apply, mem_T, Set.mem_Icc]
      by_cases h : (0:ℝ) ≤ t₁ ∧ t₁ ≤ 2 - t₂
      · rw [if_pos ⟨h.1, ht, by linarith [h.2]⟩, if_pos h]; ring
      · rw [if_neg, if_neg h]
        rintro ⟨h1, -, h3⟩
        exact h ⟨h1, by linarith⟩
    simp_rw [hind]
    rw [integral_indicator measurableSet_Icc, integral_const_mul]
  · have hz : g t₂ = 0 := hg0 t₂ (lt_of_not_ge ht)
    have hind : ∀ t₁ : ℝ, T.indicator (fun z => f z.1 * g z.2) (t₁, t₂) = 0 := by
      intro t₁
      simp only [Set.indicator_apply, mem_T]
      rw [if_neg]
      rintro ⟨-, h2, -⟩
      exact ht h2
    simp_rw [hind]
    simp [hz]

end
end Submissions.MarginalRouteK2Ceiling.NoSolution

namespace Submissions.MarginalRouteK2Ceiling.NoSolution
noncomputable section
open MeasureTheory Set Function Classical

/-- The indicator of `[0,2]`, used as the "constant 1" factor on the triangle. -/
def one2 : ℝ → ℝ := (Icc (0:ℝ) 2).indicator (fun _ => 1)

lemma one2_integrable : Integrable one2 volume := by
  rw [one2, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp) (by simp)

lemma one2_eq_one {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : one2 t = 1 := by
  rw [one2, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨h0, h2⟩)]

lemma one2_nonneg (t : ℝ) : 0 ≤ one2 t := by
  rw [one2, Set.indicator_apply]
  split <;> norm_num

lemma tri_integrable {f g : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun z : ℝ × ℝ => T.indicator (fun z => f z.1 * g z.2) z) (volume.prod volume) :=
  (hf.mul_prod hg).indicator measurableSet_T

section MargFacts

variable {F : ℝ → ℝ → ℝ}
  (hFm : AEStronglyMeasurable (uncurry F) (volume.prod volume))
  (hF2 : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ^ 2) (volume.prod volume))
  (hsupp : ∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2)

include hFm hF2 hsupp in
lemma F_integrable : Integrable (uncurry F) (volume.prod volume) := by
  have hbox : Integrable (fun z : ℝ × ℝ => one2 z.1 * one2 z.2) (volume.prod volume) :=
    one2_integrable.mul_prod one2_integrable
  refine (hF2.add hbox).mono hFm ?_
  filter_upwards with z
  show ‖F z.1 z.2‖ ≤ ‖F z.1 z.2 ^ 2 + one2 z.1 * one2 z.2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases h : F z.1 z.2 = 0
  · have p1 := one2_nonneg z.1
    have p2 := one2_nonneg z.2
    have hnn : (0:ℝ) ≤ F z.1 z.2 ^ 2 + one2 z.1 * one2 z.2 := by
      nlinarith [sq_nonneg (F z.1 z.2)]
    rw [abs_of_nonneg hnn, h]
    simp only [abs_zero]
    nlinarith
  · obtain ⟨h1, h2, h3⟩ := hsupp z.1 z.2 h
    rw [one2_eq_one h1 (by linarith), one2_eq_one h2 (by linarith)]
    have hnn : (0:ℝ) ≤ F z.1 z.2 ^ 2 + 1 * 1 := by positivity
    rw [abs_of_nonneg hnn]
    nlinarith [sq_nonneg (|F z.1 z.2| - 1), abs_nonneg (F z.1 z.2), sq_abs (F z.1 z.2)]

include hsupp in
lemma marg_sq_le {t₁ : ℝ} (hsl : Integrable (fun t₂ => F t₁ t₂ ^ 2) volume)
    (hs2 : Integrable (fun t₂ => F t₁ t₂) volume) :
    (∫ t₂, F t₁ t₂) ^ 2 ≤ 2 * ∫ t₂, F t₁ t₂ ^ 2 := by
  have hz1 : ∀ t₂ : ℝ, t₂ ∉ Icc (0:ℝ) 2 → F t₁ t₂ = 0 := by
    intro t₂ ht
    by_contra hne
    obtain ⟨h1, h2, h3⟩ := hsupp t₁ t₂ hne
    exact ht (Set.mem_Icc.mpr ⟨h2, by linarith⟩)
  have hz2 : ∀ t₂ : ℝ, t₂ ∉ Icc (0:ℝ) 2 → F t₁ t₂ ^ 2 = 0 := by
    intro t₂ ht; rw [hz1 t₂ ht]; ring
  have e1 : (∫ t₂, F t₁ t₂) = ∫ t₂ in Icc (0:ℝ) 2, F t₁ t₂ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz1).symm
  have e2 : (∫ t₂, F t₁ t₂ ^ 2) = ∫ t₂ in Icc (0:ℝ) 2, F t₁ t₂ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz2).symm
  have hvol : (volume (Icc (0:ℝ) 2)) ≠ ⊤ := by simp
  have hcs := cs_set hvol (fun t₂ => F t₁ t₂) hs2.integrableOn hsl.integrableOn
  have hv2 : (volume (Icc (0:ℝ) 2)).toReal = 2 := by simp
  rw [hv2] at hcs
  rw [e1, e2]
  exact hcs

end MargFacts

end
end Submissions.MarginalRouteK2Ceiling.NoSolution

namespace Submissions.MarginalRouteK2Ceiling.NoSolution
noncomputable section
open MeasureTheory Set Function Classical

lemma mem_T' {z : ℝ × ℝ} : z ∈ T ↔ (0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 2) := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

lemma inner_one2 {t₁ : ℝ} (h0 : 0 ≤ t₁) (h2 : t₁ ≤ 2) :
    (∫ t₂ in Icc (0:ℝ) (2 - t₁), one2 t₂) = 2 - t₁ := by
  rw [one2, setIntegral_indicator measurableSet_Icc]
  have hsub : Icc (0:ℝ) (2 - t₁) ∩ Icc (0:ℝ) 2 = Icc (0:ℝ) (2 - t₁) :=
    Set.inter_eq_self_of_subset_left (Icc_subset_Icc le_rfl (by linarith))
  rw [hsub, setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

variable {a b : ℝ}

lemma const_integrable (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s ≠ ⊤) (c : ℝ) :
    Integrable (s.indicator (fun _ => c)) volume := by
  rw [integrable_indicator_iff hs]
  exact integrableOn_const hfin (by simp)

lemma evalA {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Icc (0:ℝ) 2) {u : ℝ → ℝ}
    (hu : Integrable u volume) (hu0 : ∀ t, t ∉ S → u t = 0) :
    ∫ z, T.indicator (fun z => u z.1 * one2 z.2) z ∂(volume.prod volume)
      = ∫ t in S, u t * (2 - t) := by
  have hf0 : ∀ t : ℝ, t < 0 → u t = 0 := by
    intro t ht; exact hu0 t (fun hc => absurd (hSsub hc).1 (by linarith))
  rw [tri_int hf0 (tri_integrable hu one2_integrable)]
  have key : ∀ t₁ : ℝ, u t₁ * (∫ t₂ in Icc (0:ℝ) (2 - t₁), one2 t₂)
      = S.indicator (fun t => u t * (2 - t)) t₁ := by
    intro t₁
    by_cases ht : t₁ ∈ S
    · rw [Set.indicator_of_mem ht, inner_one2 (hSsub ht).1 (hSsub ht).2]
    · rw [Set.indicator_of_notMem ht, hu0 t₁ ht, zero_mul]
  simp_rw [key]
  rw [integral_indicator hS]

lemma evalA' {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Icc (0:ℝ) 2) {v : ℝ → ℝ}
    (hv : Integrable v volume) (hv0 : ∀ t, t ∉ S → v t = 0) :
    ∫ z, T.indicator (fun z => one2 z.1 * v z.2) z ∂(volume.prod volume)
      = ∫ t in S, v t * (2 - t) := by
  have hg0 : ∀ t : ℝ, t < 0 → v t = 0 := by
    intro t ht; exact hv0 t (fun hc => absurd (hSsub hc).1 (by linarith))
  rw [tri_int' hg0 (tri_integrable one2_integrable hv)]
  have key : ∀ t₂ : ℝ, v t₂ * (∫ t₁ in Icc (0:ℝ) (2 - t₂), one2 t₁)
      = S.indicator (fun t => v t * (2 - t)) t₂ := by
    intro t₂
    by_cases ht : t₂ ∈ S
    · rw [Set.indicator_of_mem ht, inner_one2 (hSsub ht).1 (hSsub ht).2]
    · rw [Set.indicator_of_notMem ht, hv0 t₂ ht, zero_mul]
  simp_rw [key]
  rw [integral_indicator hS]

lemma evalC (ha : 0 < a) (ha1 : a < 1) {u v : ℝ → ℝ}
    (hu : Integrable u volume) (hv : Integrable v volume)
    (hu0 : ∀ t, t ∉ Icc (0:ℝ) a → u t = 0) (hv0 : ∀ t, t ∉ Icc (0:ℝ) a → v t = 0) :
    ∫ z, T.indicator (fun z => u z.1 * v z.2) z ∂(volume.prod volume)
      = (∫ t in Icc (0:ℝ) a, u t) * (∫ t in Icc (0:ℝ) a, v t) := by
  have hf0 : ∀ t : ℝ, t < 0 → u t = 0 :=
    fun t ht => hu0 t (fun hc => absurd hc.1 (by linarith))
  rw [tri_int hf0 (tri_integrable hu hv)]
  have hvall : (∫ t, v t) = ∫ t in Icc (0:ℝ) a, v t :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hv0).symm
  have key : ∀ t₁ : ℝ, u t₁ * (∫ t₂ in Icc (0:ℝ) (2 - t₁), v t₂)
      = (Icc (0:ℝ) a).indicator (fun t => u t * (∫ s in Icc (0:ℝ) a, v s)) t₁ := by
    intro t₁
    by_cases ht : t₁ ∈ Icc (0:ℝ) a
    · rw [Set.indicator_of_mem ht]
      congr 1
      have hz : ∀ t₂ : ℝ, t₂ ∉ Icc (0:ℝ) (2 - t₁) → v t₂ = 0 := by
        intro t₂ hn
        refine hv0 t₂ (fun hc => hn (Set.mem_Icc.mpr ⟨hc.1, ?_⟩))
        have h1 := ht.2
        have h2 := hc.2
        linarith
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz, hvall]
    · rw [Set.indicator_of_notMem ht, hu0 t₁ ht, zero_mul]
  simp_rw [key]
  rw [integral_indicator measurableSet_Icc, integral_mul_const]

lemma evalD (ha : 0 < a) (ha1 : a < 1) (hb : b = 2 - a) (c : ℝ) {u : ℝ → ℝ}
    (hu : Integrable u volume) (hu0 : ∀ t, t ∉ Icc (0:ℝ) a → u t = 0) :
    ∫ z, T.indicator (fun z => u z.1 * ((Ioc b 2).indicator (fun _ => c) z.2)) z
        ∂(volume.prod volume)
      = c * ∫ t in Icc (0:ℝ) a, u t * (a - t) := by
  have hcint := const_integrable (Ioc b 2) measurableSet_Ioc (by simp) c
  have hf0 : ∀ t : ℝ, t < 0 → u t = 0 :=
    fun t ht => hu0 t (fun hc => absurd hc.1 (by linarith))
  rw [tri_int hf0 (tri_integrable hu hcint)]
  have key : ∀ t₁ : ℝ, u t₁ * (∫ t₂ in Icc (0:ℝ) (2 - t₁), (Ioc b 2).indicator (fun _ => c) t₂)
      = (Icc (0:ℝ) a).indicator (fun t => c * (u t * (a - t))) t₁ := by
    intro t₁
    by_cases ht : t₁ ∈ Icc (0:ℝ) a
    · rw [Set.indicator_of_mem ht, setIntegral_indicator measurableSet_Ioc]
      have hinter : Icc (0:ℝ) (2 - t₁) ∩ Ioc b 2 = Ioc b (2 - t₁) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
        constructor
        · rintro ⟨⟨hx0, hx1⟩, hx2, hx3⟩; exact ⟨hx2, hx1⟩
        · rintro ⟨hx1, hx2⟩
          have hbn : (0:ℝ) ≤ b := by rw [hb]; linarith
          have h1 := ht.1
          exact ⟨⟨by linarith, hx2⟩, hx1, by linarith⟩
      rw [hinter, setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by rw [hb]; linarith [ht.2]), hb]
      ring
    · rw [Set.indicator_of_notMem ht, hu0 t₁ ht, zero_mul]
  simp_rw [key]
  rw [integral_indicator measurableSet_Icc, integral_const_mul]

lemma evalE (ha : 0 < a) (ha1 : a < 1) (hb : b = 2 - a) (c : ℝ) {v : ℝ → ℝ}
    (hv : Integrable v volume) (hv0 : ∀ t, t ∉ Icc (0:ℝ) a → v t = 0) :
    ∫ z, T.indicator (fun z => ((Ioc b 2).indicator (fun _ => c) z.1) * v z.2) z
        ∂(volume.prod volume)
      = c * ∫ t in Icc (0:ℝ) a, v t * (a - t) := by
  have hcint := const_integrable (Ioc b 2) measurableSet_Ioc (by simp) c
  have hg0 : ∀ t : ℝ, t < 0 → v t = 0 :=
    fun t ht => hv0 t (fun hc => absurd hc.1 (by linarith))
  rw [tri_int' hg0 (tri_integrable hcint hv)]
  have key : ∀ t₂ : ℝ, v t₂ * (∫ t₁ in Icc (0:ℝ) (2 - t₂), (Ioc b 2).indicator (fun _ => c) t₁)
      = (Icc (0:ℝ) a).indicator (fun t => c * (v t * (a - t))) t₂ := by
    intro t₂
    by_cases ht : t₂ ∈ Icc (0:ℝ) a
    · rw [Set.indicator_of_mem ht, setIntegral_indicator measurableSet_Ioc]
      have hinter : Icc (0:ℝ) (2 - t₂) ∩ Ioc b 2 = Ioc b (2 - t₂) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
        constructor
        · rintro ⟨⟨hx0, hx1⟩, hx2, hx3⟩; exact ⟨hx2, hx1⟩
        · rintro ⟨hx1, hx2⟩
          have hbn : (0:ℝ) ≤ b := by rw [hb]; linarith
          have h1 := ht.1
          exact ⟨⟨by linarith, hx2⟩, hx1, by linarith⟩
      rw [hinter, setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by rw [hb]; linarith [ht.2]), hb]
      ring
    · rw [Set.indicator_of_notMem ht, hv0 t₂ ht, zero_mul]
  simp_rw [key]
  rw [integral_indicator measurableSet_Icc, integral_const_mul]

lemma evalF (ha : 0 < a) (ha1 : a < 1) (hb : b = 2 - a) (c d : ℝ) :
    ∫ z, T.indicator (fun z => ((Ioc b 2).indicator (fun _ => c) z.1)
        * ((Ioc b 2).indicator (fun _ => d) z.2)) z ∂(volume.prod volume) = 0 := by
  have hz : ∀ z : ℝ × ℝ, T.indicator (fun z => ((Ioc b 2).indicator (fun _ => c) z.1)
      * ((Ioc b 2).indicator (fun _ => d) z.2)) z = 0 := by
    intro z
    by_cases hzT : z ∈ T
    · rw [Set.indicator_of_mem hzT]
      obtain ⟨h1, h2, h3⟩ := mem_T'.mp hzT
      by_cases hc : z.1 ∈ Ioc b 2
      · have hd : z.2 ∉ Ioc b 2 := by
          intro hd
          have e1 := hc.1
          have e2 := hd.1
          rw [hb] at e1 e2
          linarith
        rw [Set.indicator_of_notMem hd, mul_zero]
      · rw [Set.indicator_of_notMem hc, zero_mul]
    · rw [Set.indicator_of_notMem hzT]
  simp_rw [hz]
  simp

end
end Submissions.MarginalRouteK2Ceiling.NoSolution

namespace Submissions.MarginalRouteK2Ceiling.NoSolution
noncomputable section
open MeasureTheory Set Function Classical

#check @MeasureTheory.Measure.quasiMeasurePreserving_fst
#check @MeasureTheory.Measure.quasiMeasurePreserving_snd
#check @MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving
#check @MeasureTheory.Integrable.integral_prod_right

lemma icc_int {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    (∫ t in Icc (0:ℝ) a, f t) = ∫ t in (0:ℝ)..a, f t := by
  rw [intervalIntegral.integral_of_le ha, integral_Icc_eq_integral_Ioc]

/-- One-variable core: weighted Cauchy–Schwarz. -/
theorem weighted (a : ℝ) (w : ℝ → ℝ) (ha : 0 < a)
    (h1 : IntervalIntegrable w volume 0 a)
    (h2 : IntervalIntegrable (fun t => t * w t) volume 0 a)
    (h3 : IntervalIntegrable (fun t => t * w t ^ 2) volume 0 a) :
    2 * (∫ t in (0:ℝ)..a, t * w t) ^ 2 / a ^ 2 ≤ ∫ t in (0:ℝ)..a, t * w t ^ 2 := by
  have hne : a ≠ 0 := ne_of_gt ha
  set B := ∫ t in (0:ℝ)..a, t * w t with hB
  set L : ℝ := 2 * B / a ^ 2 with hL
  have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 a :=
    (continuous_id).intervalIntegrable 0 a
  have he : (fun t : ℝ => t * (w t - L) ^ 2)
      = fun t => t * w t ^ 2 - 2 * L * (t * w t) + L ^ 2 * t := by
    funext t; ring
  have hnn : 0 ≤ ∫ t in (0:ℝ)..a, t * (w t - L) ^ 2 := by
    apply intervalIntegral.integral_nonneg ha.le
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    positivity
  have hsplit : (∫ t in (0:ℝ)..a, t * (w t - L) ^ 2)
      = (∫ t in (0:ℝ)..a, t * w t ^ 2) - 2 * L * B + L ^ 2 * (a ^ 2 / 2) := by
    rw [he, intervalIntegral.integral_add (h3.sub (h2.const_mul (2 * L))) (hid.const_mul (L ^ 2)),
        intervalIntegral.integral_sub h3 (h2.const_mul (2 * L)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_id]
    simp [hB]
  rw [hsplit] at hnn
  have hL1 : 2 * L * B = 4 * B ^ 2 / a ^ 2 := by rw [hL]; field_simp; ring
  have hL2 : L ^ 2 * (a ^ 2 / 2) = 2 * B ^ 2 / a ^ 2 := by rw [hL]; field_simp
  rw [hL1, hL2] at hnn
  have h4 : (4:ℝ) * B ^ 2 / a ^ 2 = 2 * (2 * B ^ 2 / a ^ 2) := by ring
  rw [h4] at hnn
  linarith

/-- One-variable core: the inequality the ceiling rests on. -/
theorem core (a : ℝ) (w : ℝ → ℝ) (ha : 0 < a)
    (h1 : IntervalIntegrable w volume 0 a)
    (h2 : IntervalIntegrable (fun t => t * w t) volume 0 a)
    (h3 : IntervalIntegrable (fun t => t * w t ^ 2) volume 0 a) :
    2 / a * (∫ t in (0:ℝ)..a, w t) * (∫ t in (0:ℝ)..a, t * w t)
      - (∫ t in (0:ℝ)..a, w t) ^ 2 / 2
      ≤ ∫ t in (0:ℝ)..a, t * w t ^ 2 := by
  have hne : a ≠ 0 := ne_of_gt ha
  have hw := weighted a w ha h1 h2 h3
  set A := ∫ t in (0:ℝ)..a, w t
  set B := ∫ t in (0:ℝ)..a, t * w t
  have heq : 2 * B ^ 2 / a ^ 2 - (2 / a * A * B - A ^ 2 / 2)
      = 2 * (B - a * A / 2) ^ 2 / a ^ 2 := by field_simp; ring
  have hpos : 0 ≤ 2 * (B - a * A / 2) ^ 2 / a ^ 2 := by positivity
  linarith

end
end Submissions.MarginalRouteK2Ceiling.NoSolution

namespace Submissions.MarginalRouteK2Ceiling.NoSolution
noncomputable section
open MeasureTheory Set Function Classical

lemma fst_meas {u : ℝ → ℝ} (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => u z.1) (volume.prod volume) :=
  hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst

lemma snd_meas {u : ℝ → ℝ} (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => u z.2) (volume.prod volume) :=
  hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd

lemma sq_ind (S : Set ℝ) (u : ℝ → ℝ) (t : ℝ) :
    (S.indicator u t) ^ 2 = S.indicator (fun s => u s ^ 2) t := by
  by_cases h : t ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring

section FU

variable {F : ℝ → ℝ → ℝ}
  (hFm : AEStronglyMeasurable (uncurry F) (volume.prod volume))
  (hF2 : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ^ 2) (volume.prod volume))
  (hsupp : ∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2)

include hFm hF2 hsupp in
lemma Fu_integrable {u : ℝ → ℝ} (husq : Integrable (fun t => u t ^ 2) volume)
    (hum : AEStronglyMeasurable u volume) :
    Integrable (fun z : ℝ × ℝ => F z.1 z.2 * u z.1) (volume.prod volume) := by
  have hbnd : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ^ 2 + u z.1 ^ 2 * one2 z.2)
      (volume.prod volume) := hF2.add (husq.mul_prod one2_integrable)
  refine hbnd.mono (hFm.mul (fst_meas hum)) ?_
  filter_upwards with z
  show ‖F z.1 z.2 * u z.1‖ ≤ ‖F z.1 z.2 ^ 2 + u z.1 ^ 2 * one2 z.2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases h : F z.1 z.2 = 0
  · rw [h, zero_mul, abs_zero]; exact abs_nonneg _
  · obtain ⟨h1, h2, h3⟩ := hsupp z.1 z.2 h
    rw [one2_eq_one h2 (by linarith)]
    have hnn : (0:ℝ) ≤ F z.1 z.2 ^ 2 + u z.1 ^ 2 * 1 := by positivity
    rw [abs_of_nonneg hnn, abs_mul]
    nlinarith [sq_nonneg (|F z.1 z.2| - |u z.1|), abs_nonneg (F z.1 z.2), abs_nonneg (u z.1),
      sq_abs (F z.1 z.2), sq_abs (u z.1)]

include hFm hF2 hsupp in
lemma Fv_integrable {v : ℝ → ℝ} (hvsq : Integrable (fun t => v t ^ 2) volume)
    (hvm : AEStronglyMeasurable v volume) :
    Integrable (fun z : ℝ × ℝ => F z.1 z.2 * v z.2) (volume.prod volume) := by
  have hbnd : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ^ 2 + one2 z.1 * v z.2 ^ 2)
      (volume.prod volume) := hF2.add (one2_integrable.mul_prod hvsq)
  refine hbnd.mono (hFm.mul (snd_meas hvm)) ?_
  filter_upwards with z
  show ‖F z.1 z.2 * v z.2‖ ≤ ‖F z.1 z.2 ^ 2 + one2 z.1 * v z.2 ^ 2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases h : F z.1 z.2 = 0
  · rw [h, zero_mul, abs_zero]; exact abs_nonneg _
  · obtain ⟨h1, h2, h3⟩ := hsupp z.1 z.2 h
    rw [one2_eq_one h1 (by linarith)]
    have hnn : (0:ℝ) ≤ F z.1 z.2 ^ 2 + 1 * v z.2 ^ 2 := by positivity
    rw [abs_of_nonneg hnn, abs_mul]
    nlinarith [sq_nonneg (|F z.1 z.2| - |v z.2|), abs_nonneg (F z.1 z.2), abs_nonneg (v z.2),
      sq_abs (F z.1 z.2), sq_abs (v z.2)]

include hsupp in
lemma marg_sq_le' {t₂ : ℝ} (hsl : Integrable (fun t₁ => F t₁ t₂ ^ 2) volume)
    (hs1 : Integrable (fun t₁ => F t₁ t₂) volume) :
    (∫ t₁, F t₁ t₂) ^ 2 ≤ 2 * ∫ t₁, F t₁ t₂ ^ 2 := by
  have hz1 : ∀ t₁ : ℝ, t₁ ∉ Icc (0:ℝ) 2 → F t₁ t₂ = 0 := by
    intro t₁ ht
    by_contra hne
    obtain ⟨h1, h2, h3⟩ := hsupp t₁ t₂ hne
    exact ht (Set.mem_Icc.mpr ⟨h1, by linarith⟩)
  have hz2 : ∀ t₁ : ℝ, t₁ ∉ Icc (0:ℝ) 2 → F t₁ t₂ ^ 2 = 0 := by
    intro t₁ ht; rw [hz1 t₁ ht]; ring
  have e1 : (∫ t₁, F t₁ t₂) = ∫ t₁ in Icc (0:ℝ) 2, F t₁ t₂ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz1).symm
  have e2 : (∫ t₁, F t₁ t₂ ^ 2) = ∫ t₁ in Icc (0:ℝ) 2, F t₁ t₂ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz2).symm
  have hvol : (volume (Icc (0:ℝ) 2)) ≠ ⊤ := by simp
  have hcs := cs_set hvol (fun t₁ => F t₁ t₂) hs1.integrableOn hsl.integrableOn
  have hv2 : (volume (Icc (0:ℝ) 2)).toReal = 2 := by simp
  rw [hv2] at hcs
  rw [e1, e2]
  exact hcs

end FU

end
end Submissions.MarginalRouteK2Ceiling.NoSolution

namespace Submissions.MarginalRouteK2Ceiling.NoSolution
noncomputable section
open MeasureTheory Set Function Classical

set_option maxHeartbeats 1000000 in
theorem abstract_bound {a b : ℝ} {F : ℝ → ℝ → ℝ} {G H : ℝ → ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hbdef : b = 2 - a)
    (hGdef : G = fun t₂ => ∫ t₁, F t₁ t₂)
    (hHdef : H = fun t₁ => ∫ t₂, F t₁ t₂)
    (hFm : AEStronglyMeasurable (uncurry F) (volume.prod volume))
    (hF2 : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ^ 2) (volume.prod volume))
    (hsupp : ∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2)
    (hs1 : ∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂) volume)
    (hs2 : ∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂) volume)
    (hvG : ∀ t₂ : ℝ, b < t₂ → G t₂ = 0)
    (hvH : ∀ t₁ : ℝ, b < t₁ → H t₁ = 0) :
    (∫ t in Icc (0:ℝ) a, G t ^ 2) + (∫ t in Icc (0:ℝ) a, H t ^ 2)
      ≤ 2 * ∫ z, F z.1 z.2 ^ 2 ∂(volume.prod volume) := by
  have hab : a < b := by rw [hbdef]; linarith
  have hb2 : b ≤ 2 := by rw [hbdef]; linarith
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have ha2 : a ≤ 2 := by linarith
  have hane : a ≠ 0 := ne_of_gt ha
  have hHval : ∀ t₁ : ℝ, (∫ t₂, F t₁ t₂) = H t₁ := fun t₁ => by rw [hHdef]
  have hGval : ∀ t₂ : ℝ, (∫ t₁, F t₁ t₂) = G t₂ := fun t₂ => by rw [hGdef]
  -- integrability of F and of the marginals
  have hFint : Integrable (uncurry F) (volume.prod volume) := F_integrable hFm hF2 hsupp
  have hHint : Integrable H volume := by rw [hHdef]; exact hFint.integral_prod_left
  have hGint : Integrable G volume := by rw [hGdef]; exact hFint.integral_prod_right
  have hHsupp : ∀ t : ℝ, t ∉ Icc (0:ℝ) 2 → H t = 0 := by
    intro t ht
    have hz : ∀ s : ℝ, F t s = 0 := by
      intro s
      by_contra hne
      obtain ⟨h1, h2, h3⟩ := hsupp t s hne
      exact ht (Set.mem_Icc.mpr ⟨h1, by linarith⟩)
    rw [hHdef]; simp [hz]
  have hGsupp : ∀ t : ℝ, t ∉ Icc (0:ℝ) 2 → G t = 0 := by
    intro t ht
    have hz : ∀ s : ℝ, F s t = 0 := by
      intro s
      by_contra hne
      obtain ⟨h1, h2, h3⟩ := hsupp s t hne
      exact ht (Set.mem_Icc.mpr ⟨h2, by linarith⟩)
    rw [hGdef]; simp [hz]
  have hH2 : Integrable (fun t => H t ^ 2) volume := by
    refine (hF2.integral_prod_left.const_mul 2).mono (hHint.aestronglyMeasurable.pow 2) ?_
    filter_upwards [hF2.prod_right_ae] with t₁ hsl
    have hb1 := marg_sq_le hsupp hsl (hs2 t₁)
    have hnn : (0:ℝ) ≤ ∫ t₂, F t₁ t₂ ^ 2 := integral_nonneg (fun t => sq_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ∫ t₂, F t₁ t₂ ^ 2)]
    rw [← hHval t₁]
    exact hb1
  have hG2 : Integrable (fun t => G t ^ 2) volume := by
    refine (hF2.integral_prod_right.const_mul 2).mono (hGint.aestronglyMeasurable.pow 2) ?_
    filter_upwards [hF2.prod_left_ae] with t₂ hsl
    have hb1 := marg_sq_le' hsupp hsl (hs1 t₂)
    have hnn : (0:ℝ) ≤ ∫ t₁, F t₁ t₂ ^ 2 := integral_nonneg (fun t => sq_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ∫ t₁, F t₁ t₂ ^ 2)]
    rw [← hGval t₂]
    exact hb1
  have hwt : ∀ u : ℝ → ℝ, (∀ t, t ∉ Icc (0:ℝ) 2 → u t = 0) → Integrable u volume →
      Integrable (fun t => t * u t) volume := by
    intro u hu0 hu
    refine (hu.const_mul 2).mono
      (measurable_id.aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases ht : t ∈ Icc (0:ℝ) 2
    · have h1 : |t| ≤ 2 := by rw [abs_of_nonneg ht.1]; exact ht.2
      have h2 : (0:ℝ) ≤ |u t| := abs_nonneg _
      have h3 : |(2:ℝ)| = 2 := by norm_num
      rw [h3]
      nlinarith
    · rw [hu0 t ht]; simp
  have hHt : Integrable (fun t => t * H t) volume := hwt H hHsupp hHint
  have hHt2 : Integrable (fun t => t * H t ^ 2) volume :=
    hwt (fun t => H t ^ 2) (fun t ht => by rw [hHsupp t ht]; ring) hH2
  have hGt : Integrable (fun t => t * G t) volume := hwt G hGsupp hGint
  have hGt2 : Integrable (fun t => t * G t ^ 2) volume :=
    hwt (fun t => G t ^ 2) (fun t ht => by rw [hGsupp t ht]; ring) hG2
  -- constants
  set AH := ∫ t in Icc (0:ℝ) a, H t with hAHd
  set AG := ∫ t in Icc (0:ℝ) a, G t with hAGd
  set BH := ∫ t in Icc (0:ℝ) a, t * H t with hBHd
  set BG := ∫ t in Icc (0:ℝ) a, t * G t with hBGd
  set RH := ∫ t in Icc (0:ℝ) a, t * H t ^ 2 with hRHd
  set RG := ∫ t in Icc (0:ℝ) a, t * G t ^ 2 with hRGd
  set J1 := ∫ t in Icc (0:ℝ) a, G t ^ 2 with hJ1d
  set J2 := ∫ t in Icc (0:ℝ) a, H t ^ 2 with hJ2d
  set I := ∫ z, F z.1 z.2 ^ 2 ∂(volume.prod volume) with hId
  -- the test function
  set p₁ : ℝ → ℝ := (Icc (0:ℝ) a).indicator H with hp1d
  set p₂ : ℝ → ℝ := (Ioc b 2).indicator (fun _ => -(AG / a)) with hp2d
  set q₁ : ℝ → ℝ := (Icc (0:ℝ) a).indicator G with hq1d
  set q₂ : ℝ → ℝ := (Ioc b 2).indicator (fun _ => -(AH / a)) with hq2d
  set P : ℝ → ℝ := fun t => p₁ t + p₂ t with hPd
  set Q : ℝ → ℝ := fun t => q₁ t + q₂ t with hQd
  set Θ : ℝ × ℝ → ℝ := fun z => T.indicator (fun z => P z.1 + Q z.2) z with hThd
  -- support facts
  have hp1supp : ∀ t, t ∉ Icc (0:ℝ) a → p₁ t = 0 := fun t ht => by
    rw [hp1d]; exact Set.indicator_of_notMem ht _
  have hq1supp : ∀ t, t ∉ Icc (0:ℝ) a → q₁ t = 0 := fun t ht => by
    rw [hq1d]; exact Set.indicator_of_notMem ht _
  have hdisjp : ∀ t : ℝ, p₁ t * p₂ t = 0 := by
    intro t
    by_cases ht : t ∈ Icc (0:ℝ) a
    · have hnot : t ∉ Ioc b 2 := by
        intro hc
        have e1 := hc.1
        have e2 := ht.2
        linarith
      rw [hp2d, Set.indicator_of_notMem hnot, mul_zero]
    · rw [hp1supp t ht, zero_mul]
  have hdisjq : ∀ t : ℝ, q₁ t * q₂ t = 0 := by
    intro t
    by_cases ht : t ∈ Icc (0:ℝ) a
    · have hnot : t ∉ Ioc b 2 := by
        intro hc
        have e1 := hc.1
        have e2 := ht.2
        linarith
      rw [hq2d, Set.indicator_of_notMem hnot, mul_zero]
    · rw [hq1supp t ht, zero_mul]
  -- integrability of the pieces
  have hp1i : Integrable p₁ volume := by rw [hp1d]; exact hHint.indicator measurableSet_Icc
  have hq1i : Integrable q₁ volume := by rw [hq1d]; exact hGint.indicator measurableSet_Icc
  have hp2i : Integrable p₂ volume := by
    rw [hp2d]; exact const_integrable _ measurableSet_Ioc (by simp) _
  have hq2i : Integrable q₂ volume := by
    rw [hq2d]; exact const_integrable _ measurableSet_Ioc (by simp) _
  have hp1s : Integrable (fun t => p₁ t ^ 2) volume := by
    have he : (fun t => p₁ t ^ 2) = (Icc (0:ℝ) a).indicator (fun t => H t ^ 2) := by
      funext t; rw [hp1d]; exact sq_ind _ _ t
    rw [he]; exact hH2.indicator measurableSet_Icc
  have hq1s : Integrable (fun t => q₁ t ^ 2) volume := by
    have he : (fun t => q₁ t ^ 2) = (Icc (0:ℝ) a).indicator (fun t => G t ^ 2) := by
      funext t; rw [hq1d]; exact sq_ind _ _ t
    rw [he]; exact hG2.indicator measurableSet_Icc
  have hp2s : Integrable (fun t => p₂ t ^ 2) volume := by
    have he : (fun t => p₂ t ^ 2) = (Ioc b 2).indicator (fun _ => (-(AG / a)) ^ 2) := by
      funext t; rw [hp2d]; exact sq_ind _ _ t
    rw [he]; exact const_integrable _ measurableSet_Ioc (by simp) _
  have hq2s : Integrable (fun t => q₂ t ^ 2) volume := by
    have he : (fun t => q₂ t ^ 2) = (Ioc b 2).indicator (fun _ => (-(AH / a)) ^ 2) := by
      funext t; rw [hq2d]; exact sq_ind _ _ t
    rw [he]; exact const_integrable _ measurableSet_Ioc (by simp) _
  have hPi : Integrable P volume := by rw [hPd]; exact hp1i.add hp2i
  have hQi : Integrable Q volume := by rw [hQd]; exact hq1i.add hq2i
  have hPs : Integrable (fun t => P t ^ 2) volume := by
    have he : (fun t => P t ^ 2) = fun t => p₁ t ^ 2 + p₂ t ^ 2 := by
      funext t
      have h := hdisjp t
      rw [hPd]
      simp only []
      linear_combination 2 * h
    rw [he]; exact hp1s.add hp2s
  have hQs : Integrable (fun t => Q t ^ 2) volume := by
    have he : (fun t => Q t ^ 2) = fun t => q₁ t ^ 2 + q₂ t ^ 2 := by
      funext t
      have h := hdisjq t
      rw [hQd]
      simp only []
      linear_combination 2 * h
    rw [he]; exact hq1s.add hq2s
  -- <F, Θ> = J1 + J2
  have hFP : Integrable (fun z : ℝ × ℝ => F z.1 z.2 * P z.1) (volume.prod volume) :=
    Fu_integrable hFm hF2 hsupp hPs hPi.aestronglyMeasurable
  have hFQ : Integrable (fun z : ℝ × ℝ => F z.1 z.2 * Q z.2) (volume.prod volume) :=
    Fv_integrable hFm hF2 hsupp hQs hQi.aestronglyMeasurable
  have hFTheq : (fun z : ℝ × ℝ => F z.1 z.2 * Θ z)
      = fun z => F z.1 z.2 * P z.1 + F z.1 z.2 * Q z.2 := by
    funext z
    by_cases hz : z ∈ T
    · rw [hThd]
      simp only [Set.indicator_of_mem hz]
      ring
    · have hF0 : F z.1 z.2 = 0 := by
        by_contra hne
        exact hz (mem_T'.mpr (hsupp z.1 z.2 hne))
      rw [hF0]; ring
  have hFThint : Integrable (fun z : ℝ × ℝ => F z.1 z.2 * Θ z) (volume.prod volume) := by
    rw [hFTheq]; exact hFP.add hFQ
  have hFTh : (∫ z, F z.1 z.2 * Θ z ∂(volume.prod volume)) = J1 + J2 := by
    rw [hFTheq, integral_add hFP hFQ]
    have e1 : (∫ z, F z.1 z.2 * P z.1 ∂(volume.prod volume)) = J2 := by
      rw [← integral_integral (f := fun t₁ t₂ => F t₁ t₂ * P t₁) hFP]
      have hin : ∀ t₁ : ℝ, (∫ t₂, F t₁ t₂ * P t₁)
          = (Icc (0:ℝ) a).indicator (fun s => H s ^ 2) t₁ := by
        intro t₁
        rw [integral_mul_const, hHval t₁]
        have h2 : H t₁ * p₂ t₁ = 0 := by
          by_cases ht : t₁ ∈ Ioc b 2
          · rw [hvH t₁ ht.1, zero_mul]
          · rw [hp2d, Set.indicator_of_notMem ht _, mul_zero]
        have h1 : H t₁ * p₁ t₁ = (Icc (0:ℝ) a).indicator (fun s => H s ^ 2) t₁ := by
          by_cases ht : t₁ ∈ Icc (0:ℝ) a
          · rw [hp1d, Set.indicator_of_mem ht, Set.indicator_of_mem ht]; ring
          · rw [hp1supp t₁ ht, Set.indicator_of_notMem ht _, mul_zero]
        rw [hPd]
        simp only []
        rw [mul_add, h1, h2, add_zero]
      simp_rw [hin]
      rw [integral_indicator measurableSet_Icc, hJ2d]
    have e2 : (∫ z, F z.1 z.2 * Q z.2 ∂(volume.prod volume)) = J1 := by
      rw [← integral_integral (f := fun t₁ t₂ => F t₁ t₂ * Q t₂) hFQ,
          integral_integral_swap (f := fun t₁ t₂ => F t₁ t₂ * Q t₂) hFQ]
      have hin : ∀ t₂ : ℝ, (∫ t₁, F t₁ t₂ * Q t₂)
          = (Icc (0:ℝ) a).indicator (fun s => G s ^ 2) t₂ := by
        intro t₂
        rw [integral_mul_const, hGval t₂]
        have h2 : G t₂ * q₂ t₂ = 0 := by
          by_cases ht : t₂ ∈ Ioc b 2
          · rw [hvG t₂ ht.1, zero_mul]
          · rw [hq2d, Set.indicator_of_notMem ht _, mul_zero]
        have h1 : G t₂ * q₁ t₂ = (Icc (0:ℝ) a).indicator (fun s => G s ^ 2) t₂ := by
          by_cases ht : t₂ ∈ Icc (0:ℝ) a
          · rw [hq1d, Set.indicator_of_mem ht, Set.indicator_of_mem ht]; ring
          · rw [hq1supp t₂ ht, Set.indicator_of_notMem ht _, mul_zero]
        rw [hQd]
        simp only []
        rw [mul_add, h1, h2, add_zero]
      simp_rw [hin]
      rw [integral_indicator measurableSet_Icc, hJ1d]
    rw [e1, e2]; ring
  -- Theta squared, expanded into eight triangle-products
  have hone1 : ∀ z : ℝ × ℝ, z ∈ T → one2 z.1 = 1 := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := mem_T'.mp hz
    exact one2_eq_one h1 (by linarith)
  have hone2' : ∀ z : ℝ × ℝ, z ∈ T → one2 z.2 = 1 := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := mem_T'.mp hz
    exact one2_eq_one h2 (by linarith)
  set r₁ : ℝ → ℝ := fun t => 2 * p₁ t with hr1d
  set r₂ : ℝ → ℝ := fun t => 2 * p₂ t with hr2d
  clear_value r₂ r₁ Θ Q P q₂ q₁ p₂ p₁ I J2 J1 RG RH BG BH AG AH
  have hr1i : Integrable r₁ volume := by rw [hr1d]; exact hp1i.const_mul 2
  have hr2i : Integrable r₂ volume := by rw [hr2d]; exact hp2i.const_mul 2
  have hr1supp : ∀ t, t ∉ Icc (0:ℝ) a → r₁ t = 0 := by
    intro t ht
    rw [hr1d]
    simp only []
    rw [hp1supp t ht, mul_zero]
  have hr2eq : r₂ = (Ioc b 2).indicator (fun _ => 2 * -(AG / a)) := by
    funext t
    rw [hr2d, hp2d]
    simp only []
    by_cases ht : t ∈ Ioc b 2
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht _, Set.indicator_of_notMem ht _, mul_zero]
  have hThsq : (fun z : ℝ × ℝ => Θ z ^ 2) = fun z =>
      T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
    + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z
    + T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z
    + T.indicator (fun z => one2 z.1 * q₂ z.2 ^ 2) z
    + T.indicator (fun z => r₁ z.1 * q₁ z.2) z
    + T.indicator (fun z => r₁ z.1 * q₂ z.2) z
    + T.indicator (fun z => r₂ z.1 * q₁ z.2) z
    + T.indicator (fun z => r₂ z.1 * q₂ z.2) z := by
    funext z
    by_cases hz : z ∈ T
    · rw [hThd]
      simp only [Set.indicator_of_mem hz, hone1 z hz, hone2' z hz, hPd, hQd, hr1d, hr2d]
      linear_combination 2 * hdisjp z.1 + 2 * hdisjq z.2
    · rw [hThd]
      simp only [Set.indicator_of_notMem hz]
      ring
  have i1 := tri_integrable hp1s one2_integrable
  have i2 := tri_integrable hp2s one2_integrable
  have i3 := tri_integrable one2_integrable hq1s
  have i4 := tri_integrable one2_integrable hq2s
  have i5 := tri_integrable hr1i hq1i
  have i6 := tri_integrable hr1i hq2i
  have i7 := tri_integrable hr2i hq1i
  have i8 := tri_integrable hr2i hq2i
  have h12 : Integrable (fun z : ℝ × ℝ => T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z) (volume.prod volume) :=
    i1.add i2
  have h123 : Integrable (fun z : ℝ × ℝ => T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z) (volume.prod volume) :=
    h12.add i3
  have h1234 : Integrable (fun z : ℝ × ℝ => T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z
      + T.indicator (fun z => one2 z.1 * q₂ z.2 ^ 2) z) (volume.prod volume) :=
    h123.add i4
  have h12345 : Integrable (fun z : ℝ × ℝ => T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z
      + T.indicator (fun z => one2 z.1 * q₂ z.2 ^ 2) z
      + T.indicator (fun z => r₁ z.1 * q₁ z.2) z) (volume.prod volume) :=
    h1234.add i5
  have h123456 : Integrable (fun z : ℝ × ℝ => T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z
      + T.indicator (fun z => one2 z.1 * q₂ z.2 ^ 2) z
      + T.indicator (fun z => r₁ z.1 * q₁ z.2) z
      + T.indicator (fun z => r₁ z.1 * q₂ z.2) z) (volume.prod volume) :=
    h12345.add i6
  have h1234567 : Integrable (fun z : ℝ × ℝ => T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z
      + T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z
      + T.indicator (fun z => one2 z.1 * q₂ z.2 ^ 2) z
      + T.indicator (fun z => r₁ z.1 * q₁ z.2) z
      + T.indicator (fun z => r₁ z.1 * q₂ z.2) z
      + T.indicator (fun z => r₂ z.1 * q₁ z.2) z) (volume.prod volume) :=
    h123456.add i7
  have hThsqint : Integrable (fun z : ℝ × ℝ => Θ z ^ 2) (volume.prod volume) := by
    rw [hThsq]; exact h1234567.add i8
  -- the eight evaluations
  have hIccsub : Icc (0:ℝ) a ⊆ Icc (0:ℝ) 2 := Icc_subset_Icc le_rfl ha2
  have hIocsub : Ioc b 2 ⊆ Icc (0:ℝ) 2 := fun x hx =>
    Set.mem_Icc.mpr ⟨by linarith [hx.1], hx.2⟩
  have E1 : (∫ z, T.indicator (fun z => p₁ z.1 ^ 2 * one2 z.2) z ∂(volume.prod volume))
      = ∫ t in Icc (0:ℝ) a, p₁ t ^ 2 * (2 - t) :=
    evalA measurableSet_Icc hIccsub (u := fun t => p₁ t ^ 2) hp1s
      (fun t ht => by rw [hp1supp t ht]; ring)
  have E2 : (∫ z, T.indicator (fun z => p₂ z.1 ^ 2 * one2 z.2) z ∂(volume.prod volume))
      = ∫ t in Ioc b 2, p₂ t ^ 2 * (2 - t) :=
    evalA measurableSet_Ioc hIocsub (u := fun t => p₂ t ^ 2) hp2s
      (fun t ht => by rw [hp2d, Set.indicator_of_notMem ht _]; ring)
  have E3 : (∫ z, T.indicator (fun z => one2 z.1 * q₁ z.2 ^ 2) z ∂(volume.prod volume))
      = ∫ t in Icc (0:ℝ) a, q₁ t ^ 2 * (2 - t) :=
    evalA' measurableSet_Icc hIccsub (v := fun t => q₁ t ^ 2) hq1s
      (fun t ht => by rw [hq1supp t ht]; ring)
  have E4 : (∫ z, T.indicator (fun z => one2 z.1 * q₂ z.2 ^ 2) z ∂(volume.prod volume))
      = ∫ t in Ioc b 2, q₂ t ^ 2 * (2 - t) :=
    evalA' measurableSet_Ioc hIocsub (v := fun t => q₂ t ^ 2) hq2s
      (fun t ht => by rw [hq2d, Set.indicator_of_notMem ht _]; ring)
  have E5 : (∫ z, T.indicator (fun z => r₁ z.1 * q₁ z.2) z ∂(volume.prod volume))
      = (∫ t in Icc (0:ℝ) a, r₁ t) * (∫ t in Icc (0:ℝ) a, q₁ t) :=
    evalC ha ha1 hr1i hq1i hr1supp hq1supp
  have E6 : (∫ z, T.indicator (fun z => r₁ z.1 * q₂ z.2) z ∂(volume.prod volume))
      = (-(AH / a)) * ∫ t in Icc (0:ℝ) a, r₁ t * (a - t) := by
    rw [hq2d]
    exact evalD ha ha1 hbdef (-(AH / a)) hr1i hr1supp
  have E7 : (∫ z, T.indicator (fun z => r₂ z.1 * q₁ z.2) z ∂(volume.prod volume))
      = (2 * -(AG / a)) * ∫ t in Icc (0:ℝ) a, q₁ t * (a - t) := by
    rw [hr2eq]
    exact evalE ha ha1 hbdef (2 * -(AG / a)) hq1i hq1supp
  have E8 : (∫ z, T.indicator (fun z => r₂ z.1 * q₂ z.2) z ∂(volume.prod volume)) = 0 := by
    rw [hr2eq, hq2d]
    exact evalF ha ha1 hbdef _ _
  -- the one-dimensional values
  have V1 : (∫ t in Icc (0:ℝ) a, p₁ t ^ 2 * (2 - t)) = 2 * J2 - RH := by
    have hcong : ∀ t ∈ Icc (0:ℝ) a, p₁ t ^ 2 * (2 - t) = 2 * H t ^ 2 - t * H t ^ 2 := by
      intro t ht
      rw [hp1d, Set.indicator_of_mem ht]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcong,
        integral_sub ((hH2.const_mul 2).integrableOn) (hHt2.integrableOn),
        integral_const_mul, hJ2d, hRHd]
  have hIoc2 : (∫ t in Ioc b 2, (2 - t)) = a ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hb2,
        intervalIntegral.integral_sub intervalIntegrable_const
          intervalIntegral.intervalIntegrable_id,
        intervalIntegral.integral_const, integral_id, hbdef]
    ring
  have V2 : (∫ t in Ioc b 2, p₂ t ^ 2 * (2 - t)) = AG ^ 2 / 2 := by
    have hcong : ∀ t ∈ Ioc b 2, p₂ t ^ 2 * (2 - t) = (AG / a) ^ 2 * (2 - t) := by
      intro t ht
      rw [hp2d, Set.indicator_of_mem ht]; ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcong, integral_const_mul, hIoc2]
    field_simp
  have V3 : (∫ t in Icc (0:ℝ) a, q₁ t ^ 2 * (2 - t)) = 2 * J1 - RG := by
    have hcong : ∀ t ∈ Icc (0:ℝ) a, q₁ t ^ 2 * (2 - t) = 2 * G t ^ 2 - t * G t ^ 2 := by
      intro t ht
      rw [hq1d, Set.indicator_of_mem ht]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcong,
        integral_sub ((hG2.const_mul 2).integrableOn) (hGt2.integrableOn),
        integral_const_mul, hJ1d, hRGd]
  have V4 : (∫ t in Ioc b 2, q₂ t ^ 2 * (2 - t)) = AH ^ 2 / 2 := by
    have hcong : ∀ t ∈ Ioc b 2, q₂ t ^ 2 * (2 - t) = (AH / a) ^ 2 * (2 - t) := by
      intro t ht
      rw [hq2d, Set.indicator_of_mem ht]; ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcong, integral_const_mul, hIoc2]
    field_simp
  have V5a : (∫ t in Icc (0:ℝ) a, r₁ t) = 2 * AH := by
    have hcong : ∀ t ∈ Icc (0:ℝ) a, r₁ t = 2 * H t := by
      intro t ht
      rw [hr1d]; simp only []; rw [hp1d, Set.indicator_of_mem ht]
    rw [setIntegral_congr_fun measurableSet_Icc hcong, integral_const_mul, hAHd]
  have V5b : (∫ t in Icc (0:ℝ) a, q₁ t) = AG := by
    have hcong : ∀ t ∈ Icc (0:ℝ) a, q₁ t = G t := by
      intro t ht; rw [hq1d, Set.indicator_of_mem ht]
    rw [setIntegral_congr_fun measurableSet_Icc hcong, hAGd]
  have V6 : (∫ t in Icc (0:ℝ) a, r₁ t * (a - t)) = 2 * (a * AH - BH) := by
    have hcong : ∀ t ∈ Icc (0:ℝ) a, r₁ t * (a - t) = 2 * (a * H t) - 2 * (t * H t) := by
      intro t ht
      rw [hr1d]; simp only []; rw [hp1d, Set.indicator_of_mem ht]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcong,
        integral_sub (((hHint.const_mul a).const_mul 2).integrableOn)
          ((hHt.const_mul 2).integrableOn),
        integral_const_mul, integral_const_mul, integral_const_mul, hAHd, hBHd]
    ring
  have V7 : (∫ t in Icc (0:ℝ) a, q₁ t * (a - t)) = a * AG - BG := by
    have hcong : ∀ t ∈ Icc (0:ℝ) a, q₁ t * (a - t) = a * G t - t * G t := by
      intro t ht
      rw [hq1d, Set.indicator_of_mem ht]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcong,
        integral_sub ((hGint.const_mul a).integrableOn) (hGt.integrableOn),
        integral_const_mul, hAGd, hBGd]
  -- the one-variable core, transported to set integrals
  have hcoreH : 2 / a * AH * BH - AH ^ 2 / 2 ≤ RH := by
    have h := core a H ha hHint.intervalIntegrable hHt.intervalIntegrable hHt2.intervalIntegrable
    rw [← icc_int ha.le H, ← icc_int ha.le (fun t => t * H t),
        ← icc_int ha.le (fun t => t * H t ^ 2)] at h
    rw [hAHd, hBHd, hRHd]
    exact h
  have hcoreG : 2 / a * AG * BG - AG ^ 2 / 2 ≤ RG := by
    have h := core a G ha hGint.intervalIntegrable hGt.intervalIntegrable hGt2.intervalIntegrable
    rw [← icc_int ha.le G, ← icc_int ha.le (fun t => t * G t),
        ← icc_int ha.le (fun t => t * G t ^ 2)] at h
    rw [hAGd, hBGd, hRGd]
    exact h
  have hamgm : 2 * AH * AG ≤ AH ^ 2 + AG ^ 2 := by nlinarith [sq_nonneg (AH - AG)]
  have hWle : (∫ z, Θ z ^ 2 ∂(volume.prod volume)) ≤ 2 * (J1 + J2) := by
    rw [hThsq, integral_add h1234567 i8, integral_add h123456 i7, integral_add h12345 i6,
        integral_add h1234 i5, integral_add h123 i4, integral_add h12 i3, integral_add i1 i2,
        E1, E2, E3, E4, E5, E6, E7, E8, V1, V2, V3, V4, V5a, V5b, V6, V7]
    have hx : (-(AH / a)) * (2 * (a * AH - BH)) = -2 * AH ^ 2 + 2 * (AH * BH / a) := by
      field_simp; ring
    have hy : (2 * -(AG / a)) * (a * AG - BG) = -2 * AG ^ 2 + 2 * (AG * BG / a) := by
      field_simp; ring
    have hz1 : 2 / a * AH * BH = 2 * (AH * BH / a) := by field_simp
    have hz2 : 2 / a * AG * BG = 2 * (AG * BG / a) := by field_simp
    rw [hx, hy]
    rw [hz1] at hcoreH
    rw [hz2] at hcoreG
    linarith
  have hCS : J1 + J2 ≤ I + (1/4) * (∫ z, Θ z ^ 2 ∂(volume.prod volume)) := by
    have hnn : 0 ≤ ∫ z, (F z.1 z.2 - Θ z / 2) ^ 2 ∂(volume.prod volume) :=
      integral_nonneg (fun z => sq_nonneg _)
    have he : (fun z : ℝ × ℝ => (F z.1 z.2 - Θ z / 2) ^ 2)
        = fun z => (F z.1 z.2 ^ 2 - F z.1 z.2 * Θ z) + (1/4) * Θ z ^ 2 := by
      funext z; ring
    have hsub : Integrable (fun z : ℝ × ℝ => F z.1 z.2 ^ 2 - F z.1 z.2 * Θ z)
        (volume.prod volume) := hF2.sub hFThint
    have hquart : Integrable (fun z : ℝ × ℝ => (1/4) * Θ z ^ 2) (volume.prod volume) :=
      hThsqint.const_mul (1/4)
    rw [he, integral_add hsub hquart, integral_sub hF2 hFThint, integral_const_mul, hFTh] at hnn
    rw [hId]
    linarith
  linarith [hCS, hWle]

end
end Submissions.MarginalRouteK2Ceiling.NoSolution

namespace Submissions.MarginalRouteK2Ceiling.NoSolution
noncomputable section
open MeasureTheory Set Function Classical

/-- The `k = 2`, `m = 1` marginal criterion of Polymath8b Theorem 3.14 has no solution:
the truncated squared marginals never sum to strictly more than twice the second moment. -/
theorem proof :
  ¬ ∃ (ε : ℝ) (F : ℝ → ℝ → ℝ),
    0 < ε ∧ ε < 1 ∧
    AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) ∧
    Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) ∧
    (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) ∧
    (∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂)) ∧
    (∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂)) ∧
    (∀ t₂ : ℝ, 1 + ε < t₂ → (∫ t₁, F t₁ t₂) = 0) ∧
    (∀ t₁ : ℝ, 1 + ε < t₁ → (∫ t₂, F t₁ t₂) = 0) ∧
    2 * (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume))
      < (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, F t₁ t₂) ^ 2)
        + (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, F t₁ t₂) ^ 2) := by
  rintro ⟨ε, F, hε0, hε1, hFm, hF2, hsupp, hs1, hs2, hv1, hv2, hlt⟩
  have h := abstract_bound (a := 1 - ε) (b := 1 + ε) (by linarith) (by linarith) (by ring)
    rfl rfl hFm hF2 hsupp hs1 hs2 hv1 hv2
  linarith

end
end Submissions.MarginalRouteK2Ceiling.NoSolution
