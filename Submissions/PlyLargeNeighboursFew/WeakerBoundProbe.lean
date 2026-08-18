import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Metric Set
open scoped RealInnerProductSpace

noncomputable section
namespace Submissions.PlyLargeNeighboursFew.WeakerBoundProbe

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

lemma norm_sq_sum (v : E d) : ‖v‖^2 = ∑ j, (v j)^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])

/-- Some coordinate carries at least a `1/d` share of the squared norm. -/
lemma exists_big_coord (hd : 1 ≤ d) (v : E d) : ∃ j : Fin d, ‖v‖^2 / d ≤ (v j)^2 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hsum : ∑ _j : Fin d, ‖v‖^2 / d ≤ ∑ j : Fin d, (v j)^2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← norm_sq_sum,
      mul_div_cancel₀ _ (ne_of_gt hd0)]
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨j, hj⟩

theorem large_neighbours_few (hd : 1 ≤ d) {n k : ℕ}
    (x : Fin n → E d) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hthin : ∀ p : E d, {i : Fin n | p ∈ closedBall (x i) (r i)}.ncard ≤ k)
    (i₀ : Fin n) (hmin : ∀ i, r i₀ ≤ r i) :
    {i : Fin n | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty ∧
        3 * (d:ℝ) * r i₀ ≤ r i}.ncard ≤ (2 * d + 1) * k := by
  classical
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hsd2 : (Real.sqrt d)^2 = d := Real.sq_sqrt hd0.le
  set t : ℝ := 3 * Real.sqrt d * r i₀ with ht_def
  have ht : 0 < t := by rw [ht_def]; have := hr i₀; positivity
  set Y : Fin d × Bool → E d := fun q =>
    x i₀ + ((if q.2 then t else -t)) • (EuclideanSpace.single q.1 (1:ℝ)) with hY_def
  set A : Set (Fin n) :=
    {i : Fin n | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩ closedBall (x i₀) (r i₀)).Nonempty ∧
      3 * (d:ℝ) * r i₀ ≤ r i} with hA_def
  have key : ∀ i ∈ A, x i₀ ∈ closedBall (x i) (r i) ∨ ∃ q, Y q ∈ closedBall (x i) (r i) := by
    intro i hi
    obtain ⟨-, ⟨z, hz1, hz2⟩, hbig⟩ := hi
    by_cases hin : x i₀ ∈ closedBall (x i) (r i)
    · exact Or.inl hin
    right
    set v : E d := x i - x i₀ with hv_def
    set s : ℝ := ‖v‖ with hs_def
    have hsr : r i < s := by
      simp only [mem_closedBall, dist_eq_norm, not_le] at hin
      rw [hs_def, hv_def, ← norm_neg]
      simpa using hin
    have hsub : s ≤ r i + r i₀ := by
      have h1 : dist (x i) z ≤ r i := by rw [dist_comm]; simpa [dist_comm] using hz1
      have h2 : dist z (x i₀) ≤ r i₀ := hz2
      have := dist_triangle (x i) z (x i₀)
      rw [dist_eq_norm] at this
      rw [hs_def, hv_def]
      linarith
    obtain ⟨j, hj⟩ := exists_big_coord hd v
    have hvj : s / Real.sqrt d ≤ |v j| := by
      have h1 : (s / Real.sqrt d)^2 ≤ (|v j|)^2 := by
        rw [div_pow, hsd2, sq_abs, hs_def]
        exact hj
      have h2 : (0:ℝ) ≤ s / Real.sqrt d := by
        rw [hs_def]; positivity
      nlinarith [abs_nonneg (v j)]
    refine ⟨(j, decide (0 ≤ v j)), ?_⟩
    set σ : ℝ := if decide (0 ≤ v j) = true then t else -t with hσ_def
    have hσv : σ * (v j) = t * |v j| := by
      rw [hσ_def]
      by_cases hp : 0 ≤ v j
      · simp [hp, abs_of_nonneg hp]
      · push_neg at hp
        simp [hp.not_ge, abs_of_neg hp]
    have hYi : Y (j, decide (0 ≤ v j)) - x i = σ • (EuclideanSpace.single j (1:ℝ)) - v := by
      rw [hY_def, hv_def, hσ_def]
      simp only
      abel
    have hnorm_e : ‖(EuclideanSpace.single j (1:ℝ) : E d)‖ = 1 := by
      simp [EuclideanSpace.norm_single]
    have hinner : ⟪σ • (EuclideanSpace.single j (1:ℝ) : E d), v⟫ = σ * (v j) := by
      rw [real_inner_smul_left]
      congr 1
      simp [EuclideanSpace.inner_single_left]
    have hnsq : ‖σ • (EuclideanSpace.single j (1:ℝ) : E d) - v‖^2
        = t^2 - 2 * (t * |v j|) + s^2 := by
      rw [norm_sub_sq_real, hinner, hσv, norm_smul, Real.norm_eq_abs, hnorm_e, mul_one,
        ← hs_def]
      have : |σ|^2 = t^2 := by
        rw [sq_abs, hσ_def]
        by_cases hp : 0 ≤ v j <;> simp [hp] <;> ring
      rw [this]
    have hgoal : t^2 - 2 * (t * |v j|) + s^2 ≤ (r i)^2 := by
      have h1 : t * (s / Real.sqrt d) ≤ t * |v j| := by
        exact mul_le_mul_of_nonneg_left hvj ht.le
      have h2 : t * (s / Real.sqrt d) = 3 * (r i₀) * s := by
        rw [ht_def]
        field_simp
      have h3 : s^2 - (r i)^2 ≤ 3 * r i₀ * (r i) := by
        nlinarith [hr i, hr i₀, hmin i, hsub, hsr]
      have h4 : t^2 = 9 * d * (r i₀)^2 := by
        rw [ht_def]; nlinarith [hsd2]
      nlinarith [hr i, hr i₀, hmin i, hsr, hbig]
    have : ‖Y (j, decide (0 ≤ v j)) - x i‖^2 ≤ (r i)^2 := by
      rw [hYi, hnsq]; exact hgoal
    simp only [mem_closedBall, dist_eq_norm]
    nlinarith [norm_nonneg (Y (j, decide (0 ≤ v j)) - x i), hr i]
  have hcard : ∀ p : E d, ({i : Fin n | p ∈ closedBall (x i) (r i)}).toFinset.card ≤ k := by
    intro p
    rw [← Set.ncard_eq_toFinset_card']
    exact hthin p
  set S0 : Finset (Fin n) := {i : Fin n | x i₀ ∈ closedBall (x i) (r i)}.toFinset with hS0
  set SB : Finset (Fin n) := Finset.biUnion Finset.univ (fun q : Fin d × Bool =>
      {i : Fin n | Y q ∈ closedBall (x i) (r i)}.toFinset) with hSB
  have hAsub : A.toFinset ⊆ S0 ∪ SB := by
    intro i hi
    rw [Set.mem_toFinset] at hi
    rcases key i hi with h | ⟨q, hq⟩
    · exact Finset.mem_union_left _ (by rw [hS0, Set.mem_toFinset]; exact h)
    · refine Finset.mem_union_right _ ?_
      rw [hSB]
      exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, by rw [Set.mem_toFinset]; exact hq⟩
  have hSBcard : SB.card ≤ 2 * d * k := by
    rw [hSB]
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun q _ => hcard (Y q))) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, smul_eq_mul]
    ring_nf
    omega
  calc A.ncard = A.toFinset.card := Set.ncard_eq_toFinset_card' A
    _ ≤ (S0 ∪ SB).card := Finset.card_le_card hAsub
    _ ≤ S0.card + SB.card := Finset.card_union_le _ _
    _ ≤ k + 2 * d * k := Nat.add_le_add (hcard (x i₀)) hSBcard
    _ = (2 * d + 1) * k := by ring

/-- **MUST-FAIL CONTROL.** Deliberately a *weaker* bound, `(2d+2)k` in place of `(2d+1)k`.
It is a true theorem, but it is not the canonical statement, so the anti-restatement bridge
`example : Statements.PlyLargeNeighboursFew.statement := @proof` must fail to elaborate and
this artifact must red with reason `restatement`. Its purpose is to show that the canonical
type is genuinely enforced for this label. -/
theorem proof :
    ∀ (d n k : ℕ), 1 ≤ d →
      ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        (∀ p : EuclideanSpace ℝ (Fin d),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
        ∀ i₀ : Fin n, (∀ i, r i₀ ≤ r i) →
          {i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty ∧
              3 * (d : ℝ) * r i₀ ≤ r i}.ncard
            ≤ (2 * d + 2) * k := by
  intro d n k hd x r hr hthin i₀ hmin
  refine le_trans (large_neighbours_few hd x r hr hthin i₀ hmin) ?_
  exact Nat.mul_le_mul_right k (by omega)

end Submissions.PlyLargeNeighboursFew.WeakerBoundProbe
