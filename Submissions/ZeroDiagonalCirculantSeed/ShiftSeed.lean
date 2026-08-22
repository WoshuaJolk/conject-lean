import Mathlib

namespace Submissions.ZeroDiagonalCirculantSeed.ShiftSeed

open scoped BigOperators

/-- For every `k ≥ 2` there is a `k × k` complex matrix with zero diagonal whose rows are
pairwise orthogonal with a common nonzero squared norm.

Witness: the matrix of the cyclic shift, `M i j = 1` iff `j = i + 1` in `Fin k`.  Its rows are
the standard basis vectors `e_{i+1}`, so they are orthonormal, and the diagonal vanishes because
`i + 1 ≠ i` whenever `k ≥ 2`.  (This is the circulant with first row `e_1`; its eigenvalues are
the `k`-th roots of unity, whose mean — the diagonal entry — is `0`.) -/
theorem proof :
    ∀ k : ℕ, 2 ≤ k →
      ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
        (∀ i, M i i = 0) ∧
        (∀ i j, (∑ r, star (M i r) * M j r) = if i = j then c else 0) := by
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  -- `1 ≠ 0` in `Fin (n+2)`, which is what makes the diagonal vanish.
  have hone : (1 : Fin (n + 2)) ≠ 0 := Fin.zero_ne_one.symm
  refine ⟨fun i j => if j = i + 1 then (1 : ℂ) else 0, 1, one_ne_zero, ?_, ?_⟩
  · intro i
    have : i ≠ i + 1 := by
      intro h
      have h0 : i + 0 = i + 1 := by rw [add_zero]; exact h
      exact hone (add_left_cancel h0).symm
    simp [this]
  · intro i j
    have hsum :
        (∑ r : Fin (n + 2),
            star (if r = i + 1 then (1 : ℂ) else 0) * (if r = j + 1 then (1 : ℂ) else 0))
          = if i + 1 = j + 1 then (1 : ℂ) else 0 := by
      simp [Finset.sum_ite_eq', eq_comm, mul_ite]
    rw [hsum]
    by_cases h : i = j
    · simp [h]
    · have : i + 1 ≠ j + 1 := fun hh => h (by exact add_right_cancel hh)
      simp [h, this]

end Submissions.ZeroDiagonalCirculantSeed.ShiftSeed
