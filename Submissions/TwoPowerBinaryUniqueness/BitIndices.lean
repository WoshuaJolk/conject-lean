import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic

/-!
# The binary representation is the unique minimum-size multiset of powers of two

Proof of `TwoPowerBinaryUniqueness`.  The argument is two steps.

*Minimality.*  If a multiset of exponents repeats a value `a`, replacing the two copies by
one copy of `a + 1` preserves `Σ 2^{aᵢ}` and drops the cardinality by one.  So by strong
induction on the cardinality, a multiset of exponents summing to `n` has at least
`n.bitIndices.length` elements, the base case being a repeat-free multiset, which sorts to a
strictly increasing list and is therefore literally `n.bitIndices`.

*Uniqueness.*  `(2^d - 1).bitIndices = List.range d`, of length `d`.  A multiset of `d`
exponents summing to `2^d - 1` therefore meets the minimality bound with equality, so it has
no repeat, so its sorted list is `bitIndices` of the sum, which is `List.range d`.
-/

open Nat List

namespace Submissions.TwoPowerBinaryUniqueness.BitIndices


/-- The sum of `2 ^ i` over a multiset of exponents. -/
def S (s : Multiset ℕ) : ℕ := (s.map (fun i => 2 ^ i)).sum

@[simp] theorem S_zero : S 0 = 0 := by simp [S]

@[simp] theorem S_cons (a : ℕ) (t : Multiset ℕ) : S (a ::ₘ t) = 2 ^ a + S t := by simp [S]

theorem S_coe (L : List ℕ) : S (↑L) = (L.map (fun i => 2 ^ i)).sum := by simp [S]

theorem sum_range (d : ℕ) : ((List.range d).map (fun i => 2 ^ i)).sum = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [pow_succ]
    omega

theorem bitIndices_pred (d : ℕ) : (2 ^ d - 1).bitIndices = List.range d := by
  have h := Nat.bitIndices_sum_map_two_pow (L := List.range d) (List.sortedLT_range d)
  rwa [sum_range] at h


theorem sorted_lt_of_nodup (s : Multiset ℕ) (h : s.Nodup) : (s.sort (· ≤ ·)).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  have hnd : (s.sort (· ≤ ·)).Nodup := by
    rw [← Multiset.coe_nodup, Multiset.sort_eq]; exact h
  have hle := Multiset.pairwise_sort s (· ≤ ·)
  exact List.Pairwise.imp₂ (fun _ _ hab hne => lt_of_le_of_ne hab hne) hle hnd

/-- A multiset of exponents whose powers of two sum to `n` has at least as many elements as
`n` has binary digits.  Merging a repeated exponent (`2 ^ a + 2 ^ a = 2 ^ (a+1)`) keeps the
sum and drops the count by one, so a multiset with a repeat is never minimal; a multiset
without one is the binary representation. -/
theorem bitIndices_length_le :
    ∀ (n : ℕ) (s : Multiset ℕ), Multiset.card s = n → (S s).bitIndices.length ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hcard
    by_cases hnd : s.Nodup
    · have hL := sorted_lt_of_nodup s hnd
      have hs : S s = ((s.sort (· ≤ ·)).map (fun i => 2 ^ i)).sum := by
        rw [← S_coe, Multiset.sort_eq]
      rw [hs, Nat.bitIndices_sum_map_two_pow hL]
      rw [← hcard, ← Multiset.coe_card, Multiset.sort_eq]
    · rw [Multiset.nodup_iff_count_le_one] at hnd
      push_neg at hnd
      obtain ⟨a, ha⟩ := hnd
      have hmem : a ∈ s := Multiset.count_pos.mp (by omega)
      obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem hmem
      have hmem' : a ∈ s' := by
        rw [Multiset.count_cons_self] at ha
        exact Multiset.count_pos.mp (by omega)
      obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem'
      have hct : Multiset.card ((a + 1) ::ₘ t) = n - 1 := by
        simp only [Multiset.card_cons] at hcard ⊢
        omega
      have hlt : n - 1 < n := by
        simp only [Multiset.card_cons] at hcard
        omega
      have hSt : S (a ::ₘ a ::ₘ t) = S ((a + 1) ::ₘ t) := by
        simp only [S_cons, pow_succ]
        ring
      have hle := ih (n - 1) hlt ((a + 1) ::ₘ t) hct
      rw [hSt]
      omega


theorem nodup_of_card_le (s : Multiset ℕ)
    (h : Multiset.card s ≤ (S s).bitIndices.length) : s.Nodup := by
  by_contra hnd
  rw [Multiset.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨a, ha⟩ := hnd
  have hmem : a ∈ s := Multiset.count_pos.mp (by omega)
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem hmem
  have hmem' : a ∈ s' := by
    rw [Multiset.count_cons_self] at ha
    exact Multiset.count_pos.mp (by omega)
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem'
  have hSt : S (a ::ₘ a ::ₘ t) = S ((a + 1) ::ₘ t) := by
    simp only [S_cons, pow_succ]; ring
  have hle := bitIndices_length_le (Multiset.card ((a + 1) ::ₘ t)) _ rfl
  rw [← hSt] at hle
  simp only [Multiset.card_cons] at h hle
  omega

/-- **Uniqueness of the binary representation, in the form the permutohedron needs.**
A multiset of exactly `d` exponents whose powers of two sum to `2 ^ d - 1` is exactly
`{0, 1, …, d-1}`. -/
theorem eq_range (d : ℕ) (s : Multiset ℕ) (hc : Multiset.card s = d)
    (hS : S s = 2 ^ d - 1) : s = Multiset.range d := by
  have hbi : (S s).bitIndices = List.range d := by rw [hS, bitIndices_pred]
  have hlen : (S s).bitIndices.length = d := by rw [hbi, List.length_range]
  have hnd : s.Nodup := nodup_of_card_le s (by omega)
  have hsum : S s = ((s.sort (· ≤ ·)).map (fun i => 2 ^ i)).sum := by
    rw [← S_coe, Multiset.sort_eq]
  have : s.sort (· ≤ ·) = List.range d := by
    rw [← hbi, hsum, Nat.bitIndices_sum_map_two_pow (sorted_lt_of_nodup s hnd)]
  calc s = ↑(s.sort (· ≤ ·)) := (Multiset.sort_eq s _).symm
    _ = ↑(List.range d) := by rw [this]
    _ = Multiset.range d := rfl


/-- **A multiset of exactly `d` exponents whose powers of two sum to `2 ^ d - 1` is
`{0, 1, …, d-1}`.** -/
theorem proof :
    ∀ (d : ℕ) (s : Multiset ℕ), Multiset.card s = d →
      (s.map (fun i => 2 ^ i)).sum = 2 ^ d - 1 → s = Multiset.range d :=
  fun d s hc hS => eq_range d s hc hS

end Submissions.TwoPowerBinaryUniqueness.BitIndices
