import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset

namespace Submissions.TwinPrimeSingularSeries.WeierstrassTelescope


noncomputable def g (p : ℕ) : ℝ := if 3 ≤ p then 1 / ((p : ℝ) - 1) ^ 2 else 0

theorem g_bounds (p : ℕ) : 0 ≤ g p ∧ g p ≤ 1 := by
  unfold g
  split
  · rename_i hp
    have h1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have h2 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    constructor
    · positivity
    · have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4) h2
      linarith
  · norm_num


theorem weierstrass {ι : Type*} (G : ι → ℝ) (hG : ∀ i, 0 ≤ G i ∧ G i ≤ 1) (s : Finset ι) :
    1 - ∑ i ∈ s, G i ≤ ∏ i ∈ s, (1 - G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hga := hG a
      have hprod : 0 ≤ ∏ i ∈ s, (1 - G i) :=
        Finset.prod_nonneg (fun i _ => by have := (hG i).2; linarith)
      have hsum : 0 ≤ ∑ i ∈ s, G i :=
        Finset.sum_nonneg (fun i _ => (hG i).1)
      nlinarith [ih, hprod, hsum, hga.1, hga.2]

theorem sum_inv_sq_aux : ∀ M : ℕ, 1 ≤ M →
    ∑ k ∈ Finset.Icc 1 M, (1:ℝ)/(k:ℝ)^2 ≤ 2 - 1/(M:ℝ) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      have hM0 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
      have h1 : (0:ℝ) < (M:ℝ) := by linarith
      have h2 : (0:ℝ) < (M:ℝ) + 1 := by linarith
      have hstep : (1:ℝ)/((M:ℝ)+1)^2 ≤ 1/(M:ℝ) - 1/((M:ℝ)+1) := by
        have hA : (1:ℝ)/(M:ℝ) - 1/((M:ℝ)+1) = 1/((M:ℝ)*((M:ℝ)+1)) := by
          field_simp
          ring
        rw [hA]
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith
      push_cast
      linarith [ih]

theorem sum_inv_sq (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, (1:ℝ)/(k:ℝ)^2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h := sum_inv_sq_aux N hN
    have h2 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have : (0:ℝ) < 1/(N:ℝ) := by positivity
    linarith

theorem sum_bound (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p), g p ≤ 1/2 := by
  classical
  have hsub : (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p)
      ⊆ (Finset.Icc 1 N).image (fun k => 2 * k + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hlt, hprime, hge⟩ := hp
    obtain ⟨j, hj⟩ := hprime.odd_of_ne_two (by omega)
    refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_Icc]; omega
    · omega
  have h1 : ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p), g p
      ≤ ∑ p ∈ (Finset.Icc 1 N).image (fun k => 2 * k + 1), g p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (g_bounds i).1)
  have h2 : ∑ p ∈ (Finset.Icc 1 N).image (fun k => 2 * k + 1), g p
      = ∑ k ∈ Finset.Icc 1 N, g (2 * k + 1) :=
    Finset.sum_image (fun a _ b _ hab => by omega)
  have h3 : ∑ k ∈ Finset.Icc 1 N, g (2 * k + 1) = ∑ k ∈ Finset.Icc 1 N, (1/4) * ((1:ℝ)/(k:ℝ)^2) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_Icc] at hk
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    have hk0 : (k:ℝ) ≠ 0 := by linarith
    unfold g
    rw [if_pos (by omega : 3 ≤ 2 * k + 1)]
    push_cast
    field_simp
    ring
  rw [h2, h3, ← Finset.mul_sum] at h1
  have h4 := sum_inv_sq N
  linarith

theorem lower (N : ℕ) : (1:ℝ)/4 ≤
    ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
      (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  have hcong : ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
      (1 - 1 / ((p : ℝ) - 1) ^ 2)
      = ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p), (1 - g p) := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    simp only [Finset.mem_filter] at hp
    unfold g
    rw [if_pos hp.2.2]
  rw [hcong]
  have hw := weierstrass g g_bounds ((Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p))
  have hs := sum_bound N
  linarith

theorem upper (N : ℕ) :
    ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
      (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 := by
  classical
  refine Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)
  · simp only [Finset.mem_filter] at hp
    have := g_bounds p
    unfold g at this
    rw [if_pos hp.2.2] at this
    linarith [this.2]
  · simp only [Finset.mem_filter] at hp
    have := g_bounds p
    unfold g at this
    rw [if_pos hp.2.2] at this
    linarith [this.1]

theorem at_ten :
    (∏ p ∈ (Finset.range (10 + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
      (1 - 1 / ((p : ℝ) - 1) ^ 2)) = 175 / 256 := by
  have hset : (Finset.range (10 + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p) = {3, 5, 7} := by
    decide
  rw [hset]
  norm_num

theorem proof :
  (∀ N : ℕ, (1 : ℝ) / 4 ≤
      ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2))
  ∧ (∀ N : ℕ,
      ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1)
  ∧ (∏ p ∈ (Finset.range (10 + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2)) = 175 / 256 :=
  ⟨lower, upper, at_ten⟩

end Submissions.TwinPrimeSingularSeries.WeierstrassTelescope
