import Mathlib.Analysis.InnerProductSpace.PiL2

open Metric Set

namespace Submissions.PlyGridOptimalDim1.RightEndpoint

abbrev E := EuclideanSpace ℝ (Fin 1)

/-- Unit basis vector of `ℝ¹`. -/
noncomputable def e0 : E := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

lemma norm_e0 : ‖e0‖ = 1 := by
  simp [e0, PiLp.norm_single]

lemma coord_e0 : e0.ofLp 0 = 1 := by
  simp [e0]

/-- Right-endpoint point of ball `i₀`: the point of the interval at its right end. -/
noncomputable def rightPoint (c : E) (rad : ℝ) : E := c + rad • e0

lemma rightPoint_coord (c : E) (rad : ℝ) : (rightPoint c rad).ofLp 0 = c.ofLp 0 + rad := by
  simp [rightPoint, coord_e0]

lemma rightPoint_mem (c : E) {rad : ℝ} (hrad : 0 ≤ rad) :
    rightPoint c rad ∈ closedBall c rad := by
  simp [mem_closedBall, dist_eq_norm, rightPoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hrad, norm_e0]

lemma norm_fin1 (v : E) : ‖v‖ = |v.ofLp 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs]

/-- Every neighbour of a minimum-right-endpoint ball contains that ball's right-endpoint point. -/
lemma neighbour_contains_rightPoint {n : ℕ} {x : Fin n → E} {r : Fin n → ℝ}
    {i₀ i : Fin n}
    (hmin : (x i₀).ofLp 0 + r i₀ ≤ (x i).ofLp 0 + r i)
    (hmeet : (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty) :
    rightPoint (x i₀) (r i₀) ∈ closedBall (x i) (r i) := by
  obtain ⟨z, hz_i, hz_i₀⟩ := hmeet
  have h1 : dist (x i) z ≤ r i := by
    simpa [mem_closedBall, dist_comm] using hz_i
  have h2 : dist z (x i₀) ≤ r i₀ := by
    simpa [mem_closedBall] using hz_i₀
  have htri : ‖x i - x i₀‖ ≤ r i + r i₀ := by
    have := dist_triangle (x i) z (x i₀)
    simp only [dist_eq_norm] at this h1 h2 ⊢
    linarith
  have habs : |(x i).ofLp 0 - (x i₀).ofLp 0| ≤ r i + r i₀ := by
    rwa [norm_fin1] at htri
  have hbound := abs_le.mp habs
  -- hbound.1 : - (r i + r i₀) ≤ (x i).ofLp 0 - (x i₀).ofLp 0
  -- hbound.2 : (x i).ofLp 0 - (x i₀).ofLp 0 ≤ r i + r i₀
  have hlo : (x i₀).ofLp 0 + r i₀ - (x i).ofLp 0 ≤ r i := by linarith [hmin]
  have hhi : (x i).ofLp 0 - ((x i₀).ofLp 0 + r i₀) ≤ r i := by linarith [hbound.1]
  have hcoord : |(rightPoint (x i₀) (r i₀)).ofLp 0 - (x i).ofLp 0| ≤ r i := by
    rw [rightPoint_coord, abs_le]
    exact ⟨by linarith [hhi], hlo⟩
  simpa [mem_closedBall, dist_eq_norm, norm_fin1] using hcoord

theorem proof :
    ∀ (k n : ℕ), 0 < n →
      ∀ (x : Fin n → EuclideanSpace ℝ (Fin 1)) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        Function.Injective (fun i => (x i, r i)) →
        (∀ p : EuclideanSpace ℝ (Fin 1),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀ : Fin n,
          {i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
            ≤ 2 * k := by
  intro k n hn x r hr _hinj hthin
  classical
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin n))
      (fun i => (x i).ofLp 0 + r i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  set p : E := rightPoint (x i₀) (r i₀)
  set S : Set (Fin n) :=
    {i : Fin n | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty}
  have hS_sub : S ⊆ {i : Fin n | p ∈ closedBall (x i) (r i)} := by
    intro i hi
    exact neighbour_contains_rightPoint (hmin i (Finset.mem_univ _)) hi.2
  have hcard : S.ncard ≤ k :=
    (Set.ncard_le_ncard hS_sub (Set.toFinite _)).trans (hthin p)
  exact hcard.trans (Nat.le_mul_of_pos_left k (by decide : 0 < (2 : ℕ)))

end Submissions.PlyGridOptimalDim1.RightEndpoint
