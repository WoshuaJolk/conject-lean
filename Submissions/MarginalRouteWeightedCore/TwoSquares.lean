import Mathlib

open MeasureTheory intervalIntegral

namespace Submissions.MarginalRouteWeightedCore.TwoSquares


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

theorem sharp (a : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t * (1:ℝ) ^ 2) = a ^ 2 / 2
    ∧ 2 / a * (∫ t in (0:ℝ)..a, (1:ℝ)) * (∫ t in (0:ℝ)..a, t * (1:ℝ))
        - (∫ t in (0:ℝ)..a, (1:ℝ)) ^ 2 / 2 = a ^ 2 / 2 := by
  have hne : a ≠ 0 := ne_of_gt ha
  have h1 : (∫ t in (0:ℝ)..a, t * (1:ℝ) ^ 2) = a ^ 2 / 2 := by
    simp [integral_id]
  have h2 : (∫ t in (0:ℝ)..a, (1:ℝ)) = a := by simp
  have h3 : (∫ t in (0:ℝ)..a, t * (1:ℝ)) = a ^ 2 / 2 := by simp [integral_id]
  refine ⟨h1, ?_⟩
  rw [h2, h3]
  field_simp
  ring

theorem proof :
  (∀ (a : ℝ) (w : ℝ → ℝ), 0 < a →
      IntervalIntegrable w volume 0 a →
      IntervalIntegrable (fun t => t * w t) volume 0 a →
      IntervalIntegrable (fun t => t * w t ^ 2) volume 0 a →
      2 * (∫ t in (0:ℝ)..a, t * w t) ^ 2 / a ^ 2 ≤ ∫ t in (0:ℝ)..a, t * w t ^ 2)
  ∧ (∀ (a : ℝ) (w : ℝ → ℝ), 0 < a →
      IntervalIntegrable w volume 0 a →
      IntervalIntegrable (fun t => t * w t) volume 0 a →
      IntervalIntegrable (fun t => t * w t ^ 2) volume 0 a →
      2 / a * (∫ t in (0:ℝ)..a, w t) * (∫ t in (0:ℝ)..a, t * w t)
          - (∫ t in (0:ℝ)..a, w t) ^ 2 / 2
        ≤ ∫ t in (0:ℝ)..a, t * w t ^ 2)
  ∧ (∀ a : ℝ, 0 < a →
      (∫ t in (0:ℝ)..a, t * (1:ℝ) ^ 2) = a ^ 2 / 2
      ∧ 2 / a * (∫ t in (0:ℝ)..a, (1:ℝ)) * (∫ t in (0:ℝ)..a, t * (1:ℝ))
          - (∫ t in (0:ℝ)..a, (1:ℝ)) ^ 2 / 2 = a ^ 2 / 2) :=
  ⟨weighted, core, sharp⟩

end Submissions.MarginalRouteWeightedCore.TwoSquares
