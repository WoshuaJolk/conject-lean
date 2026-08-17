import Mathlib

namespace Submissions.PlyGridOptimal.DegenerateVacuous

/-- Deliberate degenerate artifact, submitted by the poser as the RED half of the pose smoke
test required by the posing guide. It proves the root proposition with the `k`-thinness
hypothesis replaced by `False`: a vacuous restatement that closes in one line and is not the
posed proposition. Expected verdict: red, reason `restatement`. A verifier that greens this
does not constrain anything. -/
theorem proof :
    ∃ C : ℕ → ℕ,
      ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
        ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
          (∀ i, 0 < r i) →
          Function.Injective (fun i => (x i, r i)) →
          False →
          ∃ i₀ : Fin n,
            {i : Fin n | i ≠ i₀ ∧
                (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
              ≤ 2 ^ d * k + C d :=
  ⟨fun _ => 0, fun _ _ _ _ _ _ _ _ _ hf => hf.elim⟩

end Submissions.PlyGridOptimal.DegenerateVacuous
