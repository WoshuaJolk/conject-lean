import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Proof of `Statements.TauBlockSwapParity.statement`. Definitions re-declared verbatim. -/

namespace Submissions.TauBlockSwapParity.BlockSwap

def rho (k j : ℕ) : ℕ := if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2
def swapLast (k j : ℕ) : ℕ := if j = k - 1 then k else if j = k then k - 1 else j
def blk (j : ℕ) : ℕ := if j = 1 then 0 else if j % 4 = 0 then 0 else if j % 4 = 3 then 0 else 1

theorem blk_val (j : ℕ) (h : j ≠ 1) : (j % 4 = 0 ∨ j % 4 = 3) → blk j = 0 := by
  intro hj; unfold blk; rw [if_neg h]; rcases hj with h'|h' <;> simp [h']
theorem blk_val' (j : ℕ) (hne : j ≠ 1) (h : j % 4 = 1 ∨ j % 4 = 2) : blk j = 1 := by
  unfold blk; rw [if_neg hne]; rcases h with h'|h' <;> simp [h']
theorem blk_one : blk 1 = 0 := rfl

theorem v1 (k j : ℕ) (hk : 6 ≤ k) (hm : k % 4 = 2) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    blk (rho k j) + blk j = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 4 * m + 2 := ⟨k / 4, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hk1 : 4 * m + 2 - 1 = 4 * m + 1 := by omega
  rw [show rho (4*m+2) j = if j = 1 then 2 else if j = 4*m+1 then 3 else if j = 4*m+2 then 1 else j+2
        from by unfold rho; rw [hk1]]
  by_cases hA : j = 1
  · subst hA; rw [if_pos rfl, blk_val' 2 (by omega) (by omega), blk_one]
  rw [if_neg hA]
  by_cases hB : j = 4*m+1
  · subst hB; rw [if_pos rfl, blk_val 3 (by omega) (by omega), blk_val' _ (by omega) (by omega)]
  rw [if_neg hB]
  by_cases hC : j = 4*m+2
  · subst hC; rw [if_pos rfl, blk_one, blk_val' _ (by omega) (by omega)]
  rw [if_neg hC]
  have h4 : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases h4 with h|h|h|h
  · rw [blk_val' (j+2) (by omega) (by omega), blk_val j hA (by omega)]
  · rw [blk_val (j+2) (by omega) (by omega), blk_val' j hA (by omega)]
  · rw [blk_val (j+2) (by omega) (by omega), blk_val' j hA (by omega)]
  · rw [blk_val' (j+2) (by omega) (by omega), blk_val j hA (by omega)]

theorem v2 (k j : ℕ) (hk : 6 ≤ k) (hm : k % 4 = 2) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    blk (rho k (swapLast k j)) + blk j = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 4 * m + 2 := ⟨k / 4, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hk1 : 4 * m + 2 - 1 = 4 * m + 1 := by omega
  rw [show swapLast (4*m+2) j = if j = 4*m+1 then 4*m+2 else if j = 4*m+2 then 4*m+1 else j
        from by unfold swapLast; rw [hk1]]
  by_cases hB : j = 4*m+1
  · subst hB; rw [if_pos rfl]
    rw [show rho (4*m+2) (4*m+2) = 1 from by unfold rho; rw [hk1]; split_ifs <;> omega]
    rw [blk_one, blk_val' _ (by omega) (by omega)]
  rw [if_neg hB]
  by_cases hC : j = 4*m+2
  · subst hC; rw [if_pos rfl]
    rw [show rho (4*m+2) (4*m+1) = 3 from by unfold rho; rw [hk1]; split_ifs <;> omega]
    rw [blk_val 3 (by omega) (by omega), blk_val' _ (by omega) (by omega)]
  rw [if_neg hC]
  exact v1 (4*m+2) j (by omega) (by omega) h1 h2

theorem proof :
    ∀ k : ℕ, 6 ≤ k → k % 4 = 2 →
      (∀ j : ℕ, 1 ≤ j → j ≤ k → blk (rho k j) + blk j = 1) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → blk (rho k (swapLast k j)) + blk j = 1) := by
  intro k hk hm
  exact ⟨fun j a b => v1 k j hk hm a b, fun j a b => v2 k j hk hm a b⟩

end Submissions.TauBlockSwapParity.BlockSwap
