import Mathlib

namespace Submissions.TwinPrimeSingularSeries.Series

open Finset

/-- The odd primes up to `N`. -/
def OddPrimes (N : ℕ) : Finset ℕ := (range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p)

/-- The summand, extended by zero off the odd primes. -/
noncomputable def h (n : ℕ) : ℝ := if 3 ≤ n then 1 / ((n : ℝ) - 1) ^ 2 else 0

theorem h_nonneg (n : ℕ) : 0 ≤ h n := by
  unfold h; split_ifs
  · positivity
  · norm_num

theorem h_sum_bound : ∀ M : ℕ, 4 ≤ M → ∑ n ∈ range M, h n ≤ 3 / 4 - 1 / ((M : ℝ) - 2) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    norm_num [Finset.sum_range_succ, h]
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hhn : h n = 1 / ((n : ℝ) - 1) ^ 2 := by unfold h; rw [if_pos (by omega)]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hhn, hcast]
    have key : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      have h2 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hrw : (1 : ℝ) / ((n : ℝ) + 1 - 2) = 1 / ((n : ℝ) - 1) := by ring_nf
    rw [hrw]
    linarith

theorem sum_le (N : ℕ) : ∑ p ∈ OddPrimes N, 1 / ((p : ℝ) - 1) ^ 2 ≤ 3 / 4 := by
  have hstep : ∑ p ∈ OddPrimes N, 1 / ((p : ℝ) - 1) ^ 2 = ∑ p ∈ OddPrimes N, h p := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have := (Finset.mem_filter.1 hp).2.2
    unfold h; rw [if_pos this]
  rw [hstep]
  have hsub : OddPrimes N ⊆ range (max (N + 1) 4) := by
    intro p hp
    have := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
    exact Finset.mem_range.2 (by omega)
  have hle : ∑ p ∈ OddPrimes N, h p ≤ ∑ n ∈ range (max (N + 1) 4), h n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => h_nonneg i)
  refine le_trans hle ?_
  have h4 : 4 ≤ max (N + 1) 4 := le_max_right _ _
  have := h_sum_bound (max (N + 1) 4) h4
  have hM : (4 : ℝ) ≤ ((max (N + 1) 4 : ℕ) : ℝ) := by exact_mod_cast h4
  have : (0:ℝ) < 1 / (((max (N + 1) 4 : ℕ) : ℝ) - 2) := by
    apply div_pos one_pos; linarith
  linarith [h_sum_bound (max (N + 1) 4) h4]

theorem prod_one_sub (s : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hax0 : 0 ≤ a x := h0 x (Finset.mem_insert_self x s)
    have hax1 : a x ≤ 1 := h1 x (Finset.mem_insert_self x s)
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hprodnn : (0:ℝ) ≤ ∏ i ∈ s, (1 - a i) :=
      Finset.prod_nonneg (fun i hi => by linarith [h1 i (Finset.mem_insert_of_mem hi)])
    have hsumnn : (0:ℝ) ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    nlinarith

theorem proof :
    (∀ N : ℕ, (1 : ℝ) / 4 ≤
        ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
          (1 - 1 / ((p : ℝ) - 1) ^ 2))
    ∧ (∀ N : ℕ,
        ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
          (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1)
    ∧ (∏ p ∈ (Finset.range (10 + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
          (1 - 1 / ((p : ℝ) - 1) ^ 2)) = 175 / 256 := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    have h0 : ∀ i ∈ OddPrimes N, (0:ℝ) ≤ 1 / ((i : ℝ) - 1) ^ 2 := by
      intro i _; positivity
    have h1 : ∀ i ∈ OddPrimes N, (1:ℝ) / ((i : ℝ) - 1) ^ 2 ≤ 1 := by
      intro i hi
      have h3 := (Finset.mem_filter.1 hi).2.2
      have hi3 : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast h3
      rw [div_le_one (by nlinarith)]
      nlinarith
    have hb := prod_one_sub (OddPrimes N) (fun p => 1 / ((p : ℝ) - 1) ^ 2) h0 h1
    have hs := sum_le N
    show (1:ℝ) / 4 ≤ ∏ p ∈ OddPrimes N, (1 - 1 / ((p : ℝ) - 1) ^ 2)
    linarith
  · intro N
    refine Finset.prod_le_one (fun i hi => ?_) (fun i hi => ?_)
    · have h3 := (Finset.mem_filter.1 hi).2.2
      have : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast h3
      have : (1:ℝ) / ((i:ℝ) - 1) ^ 2 ≤ 1 := by
        rw [div_le_one (by nlinarith)]; nlinarith
      linarith
    · have h3 := (Finset.mem_filter.1 hi).2.2
      have : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast h3
      have : (0:ℝ) < 1 / ((i:ℝ) - 1) ^ 2 := by
        apply div_pos one_pos; nlinarith
      linarith
  · have hset : (Finset.range (10 + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p)
        = ({3, 5, 7} : Finset ℕ) := by decide
    rw [hset]
    norm_num

end Submissions.TwinPrimeSingularSeries.Series
