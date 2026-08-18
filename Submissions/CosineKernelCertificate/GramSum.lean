import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

namespace Submissions.CosineKernelCertificate.GramSum

open Matrix

theorem proof :
    ∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι]
      (c : ι → ℝ) (φ : ι → V → ℝ), (∀ j, 0 ≤ c j) →
      (Matrix.of fun u v : V => ∑ j : ι, c j * Real.cos (φ j u - φ j v)).PosSemidef := by
  intro V ι _ _ _ c φ hc
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext u v
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show φ j u - φ j v = -(φ j v - φ j u) from by ring, Real.cos_neg]
  · intro x
    have hexp : ∀ u v : V, x u * ((∑ j : ι, c j * Real.cos (φ j u - φ j v)) * x v)
        = ∑ j : ι, c j * ((x u * Real.cos (φ j u)) * (x v * Real.cos (φ j v))
            + (x u * Real.sin (φ j u)) * (x v * Real.sin (φ j v))) := by
      intro u v
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.cos_sub]; ring
    have hexp2 : ∀ u : V, ∑ v : V, x u * ((∑ j : ι, c j * Real.cos (φ j u - φ j v)) * x v)
        = ∑ j : ι, ∑ v : V, c j * ((x u * Real.cos (φ j u)) * (x v * Real.cos (φ j v))
            + (x u * Real.sin (φ j u)) * (x v * Real.sin (φ j v))) := by
      intro u
      rw [Finset.sum_congr rfl fun v _ => hexp u v, Finset.sum_comm]
    have hinner : ∀ j : ι, ∑ u : V, ∑ v : V,
        c j * ((x u * Real.cos (φ j u)) * (x v * Real.cos (φ j v))
          + (x u * Real.sin (φ j u)) * (x v * Real.sin (φ j v)))
        = c j * ((∑ u : V, x u * Real.cos (φ j u))^2
            + (∑ u : V, x u * Real.sin (φ j u))^2) := by
      intro j
      have e : ∀ u : V, ∑ v : V, c j * ((x u * Real.cos (φ j u)) * (x v * Real.cos (φ j v))
            + (x u * Real.sin (φ j u)) * (x v * Real.sin (φ j v)))
          = c j * ((x u * Real.cos (φ j u)) * (∑ v : V, x v * Real.cos (φ j v))
              + (x u * Real.sin (φ j u)) * (∑ v : V, x v * Real.sin (φ j v))) := by
        intro u
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl fun u _ => e u, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    have hval : star x ⬝ᵥ
        ((Matrix.of fun u v : V => ∑ j : ι, c j * Real.cos (φ j u - φ j v)) *ᵥ x)
        = ∑ j : ι, c j * ((∑ u : V, x u * Real.cos (φ j u))^2
            + (∑ u : V, x u * Real.sin (φ j u))^2) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, dotProduct]
      rw [Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum, hexp2 u], Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => hinner j
    rw [hval]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (by positivity)

end Submissions.CosineKernelCertificate.GramSum
