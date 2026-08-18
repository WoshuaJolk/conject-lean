import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.AdmissibleFifty246.Cert

/-- The explicit narrow admissible 50-tuple, of diameter 246. -/
def L : List ℕ :=
  [0, 2, 6, 12, 14, 20, 26, 32, 42, 44, 50, 54, 56, 60, 72, 84, 86, 90, 92, 102,
   104, 110, 116, 120, 126, 132, 134, 144, 146, 152, 156, 170, 174, 176, 180, 182,
   186, 194, 200, 204, 210, 212, 216, 222, 224, 230, 236, 240, 242, 246]

def T : Finset ℕ := L.toFinset

theorem card_T : T.card = 50 := by decide

theorem small_primes : ∀ q ∈ Finset.Ico 2 51, ∃ r ∈ Finset.range q, ∀ x ∈ L, x % q ≠ r := by
  decide

theorem proof :
    ∃ T : Finset ℕ,
      T.card = 50 ∧
      0 ∈ T ∧ 246 ∈ T ∧ (∀ x ∈ T, x ≤ 246) ∧
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) := by
  refine ⟨T, card_T, by decide, by decide, by decide, ?_⟩
  intro p hp
  by_cases hlt : p < 51
  · have h2 : 2 ≤ p := hp.two_le
    obtain ⟨r, hr, hall⟩ := small_primes p (Finset.mem_Ico.2 ⟨h2, hlt⟩)
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro x hx
    exact hall x (List.mem_toFinset.1 hx)
  · have hlt' : 51 ≤ p := Nat.not_lt.1 hlt
    have hp0 : 0 < p := hp.pos
    have hsub : T.image (· % p) ⊆ Finset.range p := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (Nat.mod_lt _ hp0)
    have hcard : (T.image (· % p)).card < (Finset.range p).card := by
      have h1 : (T.image (· % p)).card ≤ T.card := Finset.card_image_le
      rw [card_T] at h1
      rw [Finset.card_range]
      omega
    have hss : T.image (· % p) ⊂ Finset.range p :=
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, by intro h; rw [h] at hcard; omega⟩
    obtain ⟨r, hr1, hr2⟩ := Finset.exists_of_ssubset hss
    refine ⟨r, Finset.mem_range.1 hr1, ?_⟩
    intro x hx hxr
    exact hr2 (Finset.mem_image.2 ⟨x, hx, hxr⟩)

end Submissions.AdmissibleFifty246.Cert
