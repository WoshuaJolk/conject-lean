import Mathlib

namespace Statements.PlyGridOptimalDim1

/-- **Du–McCarty Problem 5.2 in dimension one: `c_1 ≤ 2`.**

Specialises the root `Statements.PlyGridOptimal` to `d = 1`. On the line, closed balls are
closed intervals; the member of least right endpoint meets every neighbour at that endpoint, so
its intersection-graph degree is at most the thinness parameter `k`, hence at most `2k = 2^1 · k`.
Additive slack is zero. -/
abbrev statement : Prop :=
  ∀ (k n : ℕ), 0 < n →
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin 1)) (r : Fin n → ℝ),
      (∀ i, 0 < r i) →
      Function.Injective (fun i => (x i, r i)) →
      (∀ p : EuclideanSpace ℝ (Fin 1),
          {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
      ∃ i₀ : Fin n,
        {i : Fin n | i ≠ i₀ ∧
            (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
          ≤ 2 * k

theorem target : statement := sorry

end Statements.PlyGridOptimalDim1
