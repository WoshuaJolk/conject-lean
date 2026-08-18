import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal NNReal

namespace Submissions.MaynardTaoM2CeilingAtTwo.CauchySchwarzCeiling

/-! ### Part 1: the one-dimensional Cauchy–Schwarz step -/

/-- If `f` vanishes off a set of measure at most `1`, then `(∫ f)² ≤ ∫ f²`.  Proved by
completing the square: `0 ≤ ∫ (f - c·1_s)² = ∫f² - 2c∫f + c²·|s|` at `c = (∫f)/|s|`. -/
lemma sq_integral_le_of_support (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hvol : volume s ≤ 1) (hsupp : ∀ x, x ∉ s → f x = 0)
    (hfm : AEStronglyMeasurable f volume)
    (hf2 : Integrable (fun x => f x ^ 2) volume) :
    (∫ x, f x) ^ 2 ≤ ∫ x, f x ^ 2 := by
  have hvolne : volume s ≠ ⊤ := by
    intro h; rw [h] at hvol; exact absurd hvol (by simp)
  set ind : ℝ → ℝ := s.indicator (fun _ => (1:ℝ)) with hind_def
  have hindval : ∀ x, x ∈ s → ind x = 1 := by intro x hx; rw [hind_def]; simp [hx]
  have hindval0 : ∀ x, x ∉ s → ind x = 0 := by intro x hx; rw [hind_def]; simp [hx]
  have hind : Integrable ind volume := by
    rw [hind_def, integrable_indicator_iff hs]
    exact integrableOn_const hvolne (by simp)
  have hindint : ∫ x, ind x = (volume s).toReal := by
    rw [hind_def, integral_indicator hs]
    simp [measureReal_def]
  have hf : Integrable f volume := by
    refine Integrable.mono' (hf2.add hind) hfm (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.add_apply]
    by_cases hx : x ∈ s
    · rw [hindval x hx, Real.norm_eq_abs]
      rcases le_or_gt |f x| 1 with h | h
      · nlinarith [sq_nonneg (f x)]
      · nlinarith [sq_abs (f x), abs_nonneg (f x)]
    · rw [hsupp x hx, hindval0 x hx]; simp
  set L := (volume s).toReal with hL_def
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hL1 : L ≤ 1 := by
    have : (volume s).toReal ≤ ((1 : ℝ≥0∞)).toReal := ENNReal.toReal_mono (by simp) hvol
    simpa [hL_def] using this
  set A := ∫ x, f x with hA
  set B := ∫ x, f x ^ 2 with hB
  have hBnn : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  rcases eq_or_lt_of_le hL0 with h | hLpos
  · have hnull : volume s = 0 := by
      have h' : (volume s).toReal = 0 := h.symm
      rcases (ENNReal.toReal_eq_zero_iff (volume s)).1 h' with h'' | h''
      · exact h''
      · exact absurd h'' hvolne
    have hae : f =ᵐ[volume] 0 := by
      have hns : ∀ᵐ x ∂volume, x ∉ s := by rw [ae_iff]; simpa using hnull
      filter_upwards [hns] with x hx using hsupp x hx
    have hA0 : A = 0 := by rw [hA, integral_congr_ae hae]; simp
    rw [hA0]; simpa using hBnn
  · set c := A / L with hc
    have hpt : ∀ x, (f x - c * ind x) ^ 2 = (f x ^ 2 - 2 * c * f x) + c ^ 2 * ind x := by
      intro x
      by_cases hx : x ∈ s
      · rw [hindval x hx]; ring
      · rw [hsupp x hx, hindval0 x hx]; ring
    have hnn : (0:ℝ) ≤ ∫ x, (f x - c * ind x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hexp : ∫ x, (f x - c * ind x) ^ 2 = B - 2 * c * A + c ^ 2 * L := by
      have hrw : (fun x => (f x - c * ind x) ^ 2)
          = (fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 * ind x) := funext hpt
      have h1 : Integrable (fun x => f x ^ 2 - 2 * c * f x) volume :=
        hf2.sub (hf.const_mul (2*c))
      have h2 : Integrable (fun x => c ^ 2 * ind x) volume := hind.const_mul _
      rw [hrw, integral_add h1 h2, integral_sub hf2 (hf.const_mul (2*c)),
        integral_const_mul, integral_const_mul, hindint]
    rw [hexp] at hnn
    have hkey : A ^ 2 ≤ L * B := by
      have hcc : c ^ 2 * L = A ^ 2 / L := by rw [hc]; field_simp; try ring
      have hca : 2 * c * A = 2 * (A ^ 2 / L) := by rw [hc]; field_simp; try ring
      rw [hcc, hca] at hnn
      have hdiv : A ^ 2 / L ≤ B := by linarith
      calc A ^ 2 = (A ^ 2 / L) * L := by field_simp
        _ ≤ B * L := by nlinarith
        _ = L * B := by ring
    nlinarith [hBnn, hL1, hkey]

/-! ### Part 2: one marginal of a function on the simplex -/

/-- For `F` supported in the strip `0 ≤ t₂ ≤ 1`, the squared marginal integrates to at most
`I(F)`.  This is `sq_integral_le_of_support` applied slicewise, with `s = [0,1]`. -/
lemma marginal_le (F : ℝ → ℝ → ℝ)
    (hm : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume))
    (hint : Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume))
    (hsupp : ∀ x y : ℝ, F x y ≠ 0 → 0 ≤ y ∧ y ≤ 1) :
    ∫ x, (∫ y, F x y) ^ 2 ≤ ∫ x, ∫ y, F x y ^ 2 := by
  have hg : Integrable (fun x => ∫ y, F x y ^ 2) volume := hint.integral_prod_left
  have hae1 : ∀ᵐ x ∂(volume : Measure ℝ), Integrable (fun y => F x y ^ 2) volume :=
    hint.prod_right_ae
  have hae2 : ∀ᵐ x ∂(volume : Measure ℝ), AEStronglyMeasurable (fun y => F x y) volume :=
    hm.prodMk_left
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hg ?_
  filter_upwards [hae1, hae2] with x hx1 hx2
  refine sq_integral_le_of_support (fun y => F x y) (Set.Icc 0 1) measurableSet_Icc ?_ ?_ hx2 hx1
  · simp
  · intro y hy
    by_contra hne
    exact hy (Set.mem_Icc.mpr ⟨(hsupp x y hne).1, (hsupp x y hne).2⟩)

/-! ### Part 3: `M₂ ≤ 2` -/

lemma m2_le_two (F : ℝ → ℝ → ℝ)
    (hm : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume))
    (hint : Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume))
    (hsupp : ∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 1) :
    (∫ t₂, (∫ t₁, F t₁ t₂) ^ 2) + (∫ t₁, (∫ t₂, F t₁ t₂) ^ 2)
      ≤ 2 * ∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume) := by
  have h2 : ∫ t₁, (∫ t₂, F t₁ t₂) ^ 2 ≤ ∫ t₁, ∫ t₂, F t₁ t₂ ^ 2 := by
    refine marginal_le F hm hint (fun x y hne => ?_)
    obtain ⟨ha, hb, hc⟩ := hsupp x y hne
    exact ⟨hb, by linarith⟩
  have hswapint : Integrable (fun p : ℝ × ℝ => F p.2 p.1 ^ 2) (volume.prod volume) := hint.swap
  have hswapm : AEStronglyMeasurable (Function.uncurry (fun y x => F x y)) (volume.prod volume) :=
    hm.prod_swap
  have h1 : ∫ t₂, (∫ t₁, F t₁ t₂) ^ 2 ≤ ∫ t₂, ∫ t₁, F t₁ t₂ ^ 2 := by
    refine marginal_le (fun y x => F x y) hswapm hswapint (fun y x hne => ?_)
    obtain ⟨ha, hb, hc⟩ := hsupp x y hne
    exact ⟨ha, by linarith⟩
  have hsw : ∫ t₂, ∫ t₁, F t₁ t₂ ^ 2 = ∫ t₁, ∫ t₂, F t₁ t₂ ^ 2 :=
    (integral_integral_swap hint).symm
  have hfub : ∫ t₁, ∫ t₂, F t₁ t₂ ^ 2 = ∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume) :=
    integral_integral hint
  rw [← hfub]
  linarith [h1, h2, hsw.le, hsw.ge]

/-! ### Part 4: no admissible triple of diameter at most 5 -/

lemma three_dvd (a : ℕ) : 3 ∣ a * (a + 2) * (a + 4) := by
  have h : ∀ x : ZMod 3, x * (x + 2) * (x + 4) = 0 := by decide
  have h2 : ((a * (a + 2) * (a + 4) : ℕ) : ZMod 3) = 0 := by
    push_cast
    exact h (a : ZMod 3)
  exact (ZMod.natCast_eq_zero_iff _ _).mp h2

lemma no_admissible_triple_of_small_diameter (h₁ h₂ h₃ : ℕ)
    (h12 : h₁ < h₂) (h23 : h₂ < h₃) (hd : h₃ ≤ h₁ + 5) :
    ¬ (∀ p : ℕ, Nat.Prime p →
        ∃ a : ℕ, ¬ p ∣ (a + h₁) ∧ ¬ p ∣ (a + h₂) ∧ ¬ p ∣ (a + h₃)) := by
  intro hadm
  -- admissibility at 2 forces all three shifts into one parity class
  obtain ⟨a₂, k1, k2, k3⟩ := hadm 2 Nat.prime_two
  have hshape : h₂ = h₁ + 2 ∧ h₃ = h₁ + 4 := by omega
  obtain ⟨e2, e3⟩ := hshape
  -- admissibility at 3 then contradicts 3 ∣ n(n+2)(n+4)
  obtain ⟨a, m1, m2, m3⟩ := hadm 3 (by norm_num)
  have h3p : Nat.Prime 3 := by norm_num
  have hdvd : 3 ∣ (a + h₁) * ((a + h₁) + 2) * ((a + h₁) + 4) := three_dvd (a + h₁)
  rcases (Nat.Prime.dvd_mul h3p).mp hdvd with hx | hx
  · rcases (Nat.Prime.dvd_mul h3p).mp hx with hy | hy
    · exact m1 hy
    · exact m2 (by rw [e2]; omega)
  · exact m3 (by rw [e3]; omega)

/-! ### The conjunction -/

theorem proof :
    (∀ F : ℝ → ℝ → ℝ,
        AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
        Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) (volume.prod volume) →
        (∀ t₁ t₂ : ℝ, F t₁ t₂ ≠ 0 → 0 ≤ t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 1) →
        (∫ t₂, (∫ t₁, F t₁ t₂) ^ 2) + (∫ t₁, (∫ t₂, F t₁ t₂) ^ 2)
          ≤ 2 * ∫ p : ℝ × ℝ, F p.1 p.2 ^ 2 ∂(volume.prod volume)) ∧
    (∀ h₁ h₂ h₃ : ℕ, h₁ < h₂ → h₂ < h₃ → h₃ ≤ h₁ + 5 →
        ¬ (∀ p : ℕ, Nat.Prime p →
            ∃ a : ℕ, ¬ p ∣ (a + h₁) ∧ ¬ p ∣ (a + h₂) ∧ ¬ p ∣ (a + h₃)))  :=
  ⟨m2_le_two, no_admissible_triple_of_small_diameter⟩

end Submissions.MaynardTaoM2CeilingAtTwo.CauchySchwarzCeiling
