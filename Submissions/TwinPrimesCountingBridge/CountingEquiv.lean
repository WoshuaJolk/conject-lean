import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

namespace Submissions.TwinPrimesCountingBridge.CountingEquiv

theorem proof :
  (∀ M : ℕ, ∃ T : Finset ℕ, M ≤ T.card ∧ ∀ p ∈ T, Nat.Prime p ∧ Nat.Prime (p + 2))
    ↔ (∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  constructor
  · intro h N
    obtain ⟨T, hcard, hmem⟩ := h (N + 2)
    by_contra hcon
    push_neg at hcon
    have hsub : T ⊆ Finset.range (N + 1) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hmem p hp
      have := hcon p
      rw [Finset.mem_range]
      by_contra hge
      exact absurd (this (by omega) hp1) (by simpa using hp2)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    omega
  · intro h M
    induction M with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨T, hcard, hmem⟩ := ih
      obtain ⟨p, hpgt, hp1, hp2⟩ := h (T.sup id)
      have hnot : p ∉ T := by
        intro hp
        have : id p ≤ T.sup id := Finset.le_sup hp
        simp only [id] at this
        omega
      refine ⟨insert p T, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot]; omega
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ⟨hp1, hp2⟩
        · exact hmem q hq

end Submissions.TwinPrimesCountingBridge.CountingEquiv
