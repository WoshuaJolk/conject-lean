import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

namespace Submissions.ThetaCliqueCertificates.WeakDuality

open Matrix Commons

/-- The Frobenius pairing of two positive semidefinite real matrices is nonnegative. -/
theorem trace_mul_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {M X : Matrix V V ℝ} (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace := by
  classical
  have hH : M.IsHermitian := hM.isHermitian
  set U : Matrix V V ℝ := (Matrix.IsHermitian.eigenvectorUnitary hH : Matrix V V ℝ) with hU
  set D : Matrix V V ℝ := Matrix.diagonal (RCLike.ofReal ∘ Matrix.IsHermitian.eigenvalues hH)
    with hD
  have hMe : M = U * D * star U := by
    conv_lhs => rw [Matrix.IsHermitian.spectral_theorem hH]
    rw [Unitary.conjStarAlgAut_apply]
  have hY : ((star U) * X * U).PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hX U
    rwa [← Matrix.star_eq_conjTranspose] at h
  have htr : (M * X).trace = (D * ((star U) * X * U)).trace := by
    rw [hMe, Matrix.trace_mul_comm]
    have e1 : X * (U * D * star U) = (X * U * D) * star U := by simp [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    have e2 : star U * (X * U * D) = (star U * X * U) * D := by simp [Matrix.mul_assoc]
    rw [e2, Matrix.trace_mul_comm]
  rw [htr]
  have hdiag : (D * ((star U) * X * U)).trace
      = ∑ i, Matrix.IsHermitian.eigenvalues hH i * ((star U) * X * U) i i := by
    simp [Matrix.trace, Matrix.mul_apply, hD, Matrix.diagonal_apply, Finset.sum_ite_eq]
  rw [hdiag]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Matrix.PosSemidef.diag_nonneg hY)
  exact Matrix.PosSemidef.eigenvalues_nonneg hM i

section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weak duality: an upper certificate bounds every feasible value. -/
theorem feasible_le {adj : V → V → Prop} {A : Matrix V V ℝ} {t : ℝ}
    (hd : ∀ u, A u u = 1) (he : ∀ u v, adj u v → A u v = 1)
    (hpsd : (t • (1 : Matrix V V ℝ) - A).PosSemidef) :
    ∀ s ∈ thetaCliqueFeasible adj, s ≤ t := by
  rintro s ⟨X, hX, htr, hzero, rfl⟩
  have hkey : 0 ≤ ((t • (1 : Matrix V V ℝ) - A) * X).trace := trace_mul_nonneg hpsd hX
  have hsym : ∀ u v : V, X u v = X v u := by
    intro u v
    have h := congrFun (congrFun hX.isHermitian u) v
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hpt : ∀ u v : V, (t • (1 : Matrix V V ℝ) - A) u v * X v u
      = t * (if u = v then X u u else 0) - X u v := by
    intro u v
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : u = v
    · subst h
      rw [hd u]
      simp
      ring
    · by_cases hadj : adj u v
      · rw [he u v hadj, ← hsym u v]
        simp only [if_neg h]
        ring
      · rw [← hsym u v, hzero u v h hadj]
        simp only [if_neg h]
        ring
  have hetr : ((t • (1 : Matrix V V ℝ) - A) * X).trace
      = ∑ u : V, ∑ v : V, (t • (1 : Matrix V V ℝ) - A) u v * X v u := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  have hrow : ∀ u : V, ∑ v : V, (t • (1 : Matrix V V ℝ) - A) u v * X v u
      = t * X u u - ∑ v : V, X u v := by
    intro u
    rw [Finset.sum_congr rfl fun v _ => hpt u v, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.mul_sum]
    simp
  have htr' : ∑ u : V, X u u = 1 := by rw [← htr]; simp [Matrix.trace, Matrix.diag_apply]
  rw [hetr, Finset.sum_congr rfl fun u _ => hrow u, Finset.sum_sub_distrib, ← Finset.mul_sum,
    htr'] at hkey
  linarith

end

theorem proof :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (adj : V → V → Prop)
      (A : Matrix V V ℝ) (t : ℝ), 0 ≤ t →
      (∀ u, A u u = 1) → (∀ u v, adj u v → A u v = 1) →
      (t • (1 : Matrix V V ℝ) - A).PosSemidef →
      Commons.thetaClique adj ≤ t ∧
        ∀ X : Matrix V V ℝ, X.PosSemidef → X.trace = 1 →
          (∀ u v, u ≠ v → ¬ adj u v → X u v = 0) →
          (∑ u, ∑ v, X u v) ≤ Commons.thetaClique adj := by
  intro V _ _ adj A t ht hd he hpsd
  have hb := feasible_le (adj := adj) hd he hpsd
  refine ⟨Real.sSup_le hb ht, ?_⟩
  intro X hX htr hzero
  exact le_csSup ⟨t, fun _ hx => hb _ hx⟩ ⟨X, hX, htr, hzero, rfl⟩

end Submissions.ThetaCliqueCertificates.WeakDuality
