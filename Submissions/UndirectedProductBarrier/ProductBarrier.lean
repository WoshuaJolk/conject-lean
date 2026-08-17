import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Submissions.UndirectedProductBarrier.ProductBarrier

abbrev statement : Prop :=
  ∀ k k₁ k₂ : ℕ, 4 ≤ k → 2 ≤ k₁ → 2 ≤ k₂ → k = k₁ * k₂ →
    ((k : ℝ) - 1) / ((k : ℝ) - 2) < (k₁ : ℝ) / ((k₁ : ℝ) - 1) ∧
    ((k : ℝ) - 1) / ((k : ℝ) - 2) < (k₂ : ℝ) / ((k₂ : ℝ) - 1)

theorem key (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (a * b - 1) / (a * b - 2) < a / (a - 1) := by
  have ha1 : (0:ℝ) < a - 1 := by linarith
  have hab : (0:ℝ) < a * b - 2 := by nlinarith
  rw [div_lt_div_iff₀ hab ha1]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - 2) (by linarith : (0:ℝ) ≤ b - 1)]

theorem proof : statement := by
  intro k k₁ k₂ _ h1 h2 hk
  have h1' : (2:ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast h1
  have h2' : (2:ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast h2
  have hk' : (k : ℝ) = (k₁ : ℝ) * (k₂ : ℝ) := by rw [hk]; push_cast; ring
  rw [hk']
  refine ⟨key _ _ h1' h2', ?_⟩
  rw [mul_comm]
  exact key _ _ h2' h1'

end Submissions.UndirectedProductBarrier.ProductBarrier
