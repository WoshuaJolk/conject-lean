import Mathlib

namespace Submissions.PlyRootNonVacuous.Poser

/-- One ball of radius `1` centred at the origin is a non-empty injective family, and it is
`k`-thin for every `k ≥ 1` because it has one member. -/
theorem proof :
    ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
      ∃ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
        0 < n ∧
        (∀ i, 0 < r i) ∧
        Function.Injective (fun i => (x i, r i)) ∧
        ∀ p : EuclideanSpace ℝ (Fin d),
          {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k := by
  intro d k _ hk
  refine ⟨1, fun _ => 0, fun _ => 1, Nat.one_pos, fun _ => one_pos, ?_, ?_⟩
  · intro a b _; exact Subsingleton.elim a b
  · intro p
    have h := Set.ncard_le_ncard
      (Set.subset_univ {i : Fin 1 | p ∈ Metric.closedBall
        ((fun _ => (0 : EuclideanSpace ℝ (Fin d))) i) ((fun _ => (1 : ℝ)) i)})
      Set.finite_univ
    have h1 : {i : Fin 1 | p ∈ Metric.closedBall
        ((fun _ => (0 : EuclideanSpace ℝ (Fin d))) i) ((fun _ => (1 : ℝ)) i)}.ncard ≤ 1 := by
      simpa using h
    exact le_trans h1 hk

end Submissions.PlyRootNonVacuous.Poser
