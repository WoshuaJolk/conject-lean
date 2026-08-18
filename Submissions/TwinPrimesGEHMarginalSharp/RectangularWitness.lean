import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory

namespace Submissions.TwinPrimesGEHMarginalSharp.RectangularWitness

noncomputable def chi (a b : ℝ) : ℝ → ℝ := Set.indicator (Set.Ico a b) (fun _ => (1:ℝ))

lemma chi_mem {a b x : ℝ} (h : x ∈ Set.Ico a b) : chi a b x = 1 := Set.indicator_of_mem h _
lemma chi_not_mem {a b x : ℝ} (h : x ∉ Set.Ico a b) : chi a b x = 0 :=
  Set.indicator_of_notMem h _

lemma chi_meas (a b : ℝ) : Measurable (chi a b) :=
  measurable_const.indicator measurableSet_Ico

lemma chi_integrable (a b : ℝ) : Integrable (chi a b) volume := by
  unfold chi
  rw [integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by simp) (by simp)

lemma chi_integral {a b : ℝ} (h : a ≤ b) : ∫ x, chi a b x = b - a := by
  unfold chi
  rw [integral_indicator measurableSet_Ico, setIntegral_const, measureReal_def,
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  simp

lemma chi_sq (a b x : ℝ) : (chi a b x) ^ 2 = chi a b x := by
  by_cases h : x ∈ Set.Ico a b
  · rw [chi_mem h]; norm_num
  · rw [chi_not_mem h]; norm_num


/-! ### The sign-flipped thin strip -/

noncomputable def sgn (d : ℝ) : ℝ → ℝ := fun t => chi 0 (d/2) t - chi (d/2) d t

lemma sgn_meas (d : ℝ) : Measurable (sgn d) := (chi_meas _ _).sub (chi_meas _ _)

lemma sgn_integrable (d : ℝ) : Integrable (sgn d) volume :=
  (chi_integrable _ _).sub (chi_integrable _ _)

lemma sgn_integral {d : ℝ} (hd : 0 ≤ d) : ∫ t, sgn d t = 0 := by
  unfold sgn
  rw [integral_sub (chi_integrable _ _) (chi_integrable _ _), chi_integral (by linarith),
    chi_integral (by linarith)]
  ring

lemma sgn_sq {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : (sgn d t) ^ 2 = chi 0 d t := by
  unfold sgn
  rcases lt_or_ge t 0 with h | h
  · rw [chi_not_mem (by simp [Set.mem_Ico]; intro h'; linarith),
      chi_not_mem (by simp [Set.mem_Ico]; intro h'; linarith),
      chi_not_mem (by simp [Set.mem_Ico]; intro h'; linarith)]
    norm_num
  rcases lt_or_ge t (d/2) with h2 | h2
  · rw [chi_mem (Set.mem_Ico.2 ⟨h, h2⟩), chi_not_mem (by simp [Set.mem_Ico]; intro h'; linarith),
      chi_mem (Set.mem_Ico.2 ⟨h, by linarith⟩)]
    norm_num
  rcases lt_or_ge t d with h3 | h3
  · rw [chi_not_mem (by simp [Set.mem_Ico]; intro _; linarith),
      chi_mem (Set.mem_Ico.2 ⟨h2, h3⟩), chi_mem (Set.mem_Ico.2 ⟨h, h3⟩)]
    norm_num
  · rw [chi_not_mem (by simp [Set.mem_Ico]; intro _; linarith),
      chi_not_mem (by simp [Set.mem_Ico]; intro _; linarith),
      chi_not_mem (by simp [Set.mem_Ico]; intro _; linarith)]
    norm_num

lemma sgn_zero_of_ge {d t : ℝ} (h : d ≤ t) : sgn d t = 0 := by
  unfold sgn
  rw [chi_not_mem (by simp [Set.mem_Ico]; intro _; linarith),
    chi_not_mem (by simp [Set.mem_Ico]; intro _; linarith)]
  ring


lemma sgn_zero_of_neg {d t : ℝ} (h : t < 0) : sgn d t = 0 := by
  unfold sgn
  rw [chi_not_mem (by simp [Set.mem_Ico]; intro h'; linarith),
    chi_not_mem (by simp [Set.mem_Ico]; intro h'; linarith)]
  ring

/-! ### The witness -/

theorem proof' (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : c < 2) :
    ∃ F : ℝ → ℝ → ℝ,
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) ∧
      Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) ∧
      (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) ∧
      (∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂)) ∧
      (∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂)) ∧
      (∀ t₂ : ℝ, 1 + ε < t₂ → (∫ t₁, F t₁ t₂) = 0) ∧
      (∀ t₁ : ℝ, 1 + ε < t₁ → (∫ t₂, F t₁ t₂) = 0) ∧
      0 < (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume)) ∧
      c * (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume))
        < (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, F t₁ t₂) ^ 2)
          + (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, F t₁ t₂) ^ 2) := by
  have h2c : (0:ℝ) < 2 - c := by linarith
  have h1e : (0:ℝ) < 1 - ε := by linarith
  set d : ℝ := min (2 - c) (1 - ε) / 2 with hd_def
  have hd0 : 0 < d := by
    rw [hd_def]; have := lt_min h2c h1e; linarith
  have hdc : d < 2 - c := by
    rw [hd_def]; have : min (2 - c) (1 - ε) ≤ 2 - c := min_le_left _ _; linarith
  have hde : d ≤ 1 - ε := by
    rw [hd_def]; have : min (2 - c) (1 - ε) ≤ 1 - ε := min_le_right _ _; linarith
  have hd2 : d < 2 := by linarith
  refine ⟨fun t₁ t₂ => chi 0 (2 - d) t₁ * sgn d t₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((chi_meas 0 (2 - d)).comp measurable_fst).mul
      ((sgn_meas d).comp measurable_snd)).aestronglyMeasurable
  · have hfun : (fun p : ℝ × ℝ => (chi 0 (2 - d) p.1 * sgn d p.2) ^ 2)
        = fun p : ℝ × ℝ => chi 0 (2 - d) p.1 * chi 0 d p.2 :=
      funext fun p => by rw [mul_pow, chi_sq, sgn_sq hd0.le]
    rw [hfun]
    exact (chi_integrable 0 (2 - d)).mul_prod (chi_integrable 0 d)
  · intro t₁ t₂ hne
    dsimp only at hne
    have h1 : chi 0 (2 - d) t₁ ≠ 0 := fun h => hne (by rw [h]; ring)
    have h2 : sgn d t₂ ≠ 0 := fun h => hne (by rw [h]; ring)
    have hm1 : t₁ ∈ Set.Ico (0:ℝ) (2 - d) := by
      by_contra hcon; exact h1 (chi_not_mem hcon)
    have hm2 : 0 ≤ t₂ ∧ t₂ < d := by
      constructor
      · by_contra hcon; exact h2 (sgn_zero_of_neg (by linarith [not_le.1 hcon]))
      · by_contra hcon; exact h2 (sgn_zero_of_ge (not_lt.1 hcon))
    obtain ⟨ha, hb⟩ := Set.mem_Ico.1 hm1
    exact ⟨ha, hm2.1, by linarith [hm2.2]⟩
  · intro t₂; exact (chi_integrable 0 (2 - d)).mul_const _
  · intro t₁; exact (sgn_integrable d).const_mul _
  · intro t₂ ht
    rw [integral_mul_const, chi_integral (by linarith),
      sgn_zero_of_ge (by linarith), mul_zero]
  · intro t₁ _
    rw [integral_const_mul, sgn_integral hd0.le, mul_zero]
  · have hfun : (fun p : ℝ × ℝ => (chi 0 (2 - d) p.1 * sgn d p.2) ^ 2)
        = fun p : ℝ × ℝ => chi 0 (2 - d) p.1 * chi 0 d p.2 :=
      funext fun p => by rw [mul_pow, chi_sq, sgn_sq hd0.le]
    rw [hfun, integral_prod_mul, chi_integral (by linarith), chi_integral hd0.le]
    have : (2:ℝ) - d - 0 = 2 - d := by ring
    nlinarith
  · have hfun : (fun p : ℝ × ℝ => (chi 0 (2 - d) p.1 * sgn d p.2) ^ 2)
        = fun p : ℝ × ℝ => chi 0 (2 - d) p.1 * chi 0 d p.2 :=
      funext fun p => by rw [mul_pow, chi_sq, sgn_sq hd0.le]
    have hI : (∫ p : ℝ × ℝ, (chi 0 (2 - d) p.1 * sgn d p.2) ^ 2 ∂(volume.prod volume))
        = (2 - d) * d := by
      rw [hfun, integral_prod_mul, chi_integral (by linarith), chi_integral hd0.le]
      ring
    have hm2 : ∀ t₁ : ℝ, (∫ t₂, chi 0 (2 - d) t₁ * sgn d t₂) = 0 := by
      intro t₁; rw [integral_const_mul, sgn_integral hd0.le, mul_zero]
    have hJ2 : (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, chi 0 (2 - d) t₁ * sgn d t₂) ^ 2) = 0 := by
      simp [hm2]
    have hm1 : ∀ t₂ : ℝ, (∫ t₁, chi 0 (2 - d) t₁ * sgn d t₂) = (2 - d) * sgn d t₂ := by
      intro t₂; rw [integral_mul_const, chi_integral (by linarith)]; ring
    have hchi_out : ∀ x : ℝ, x ∉ Set.Icc (0:ℝ) (1 - ε) → chi 0 d x = 0 := by
      intro x hx
      refine chi_not_mem (fun hmem => hx ?_)
      obtain ⟨ha, hb⟩ := Set.mem_Ico.1 hmem
      exact Set.mem_Icc.2 ⟨ha, by linarith⟩
    have hJ1 : (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, chi 0 (2 - d) t₁ * sgn d t₂) ^ 2)
        = (2 - d) ^ 2 * d := by
      have hstep : (fun t₂ : ℝ => (∫ t₁, chi 0 (2 - d) t₁ * sgn d t₂) ^ 2)
          = fun t₂ : ℝ => (2 - d) ^ 2 * chi 0 d t₂ :=
        funext fun t₂ => by rw [hm1 t₂, mul_pow, sgn_sq hd0.le]
      rw [hstep, integral_const_mul,
        setIntegral_eq_integral_of_forall_compl_eq_zero hchi_out, chi_integral hd0.le]
      ring
    rw [hI, hJ1, hJ2]
    have hkey : 0 < (2 - d) * d * (2 - d - c) :=
      mul_pos (mul_pos (by linarith) hd0) (by linarith)
    nlinarith [hkey]

/-- The statement in the exact shape the verifier demands. -/
theorem proof :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ c : ℝ, c < 2 →
      ∃ F : ℝ → ℝ → ℝ,
        AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) ∧
        Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) ∧
        (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 2) ∧
        (∀ t₂ : ℝ, Integrable (fun t₁ => F t₁ t₂)) ∧
        (∀ t₁ : ℝ, Integrable (fun t₂ => F t₁ t₂)) ∧
        (∀ t₂ : ℝ, 1 + ε < t₂ → (∫ t₁, F t₁ t₂) = 0) ∧
        (∀ t₁ : ℝ, 1 + ε < t₁ → (∫ t₂, F t₁ t₂) = 0) ∧
        0 < (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume)) ∧
        c * (∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume))
          < (∫ t₂ in Set.Icc (0:ℝ) (1 - ε), (∫ t₁, F t₁ t₂) ^ 2)
            + (∫ t₁ in Set.Icc (0:ℝ) (1 - ε), (∫ t₂, F t₁ t₂) ^ 2) :=
  fun ε h1 h2 c h3 => proof' ε h1 h2 c h3

end Submissions.TwinPrimesGEHMarginalSharp.RectangularWitness
