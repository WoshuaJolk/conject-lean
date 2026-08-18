import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Filter.Cofinite

open Filter

namespace Submissions.TwinPrimesH1Attained.LiminfAttained


noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

theorem liminf_attained (u : ℕ → ℕ∞) (m : ℕ)
    (h : Filter.liminf u Filter.atTop = (m : ℕ∞)) :
    (∀ᶠ n in Filter.atTop, (m : ℕ∞) ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = (m : ℕ∞)) := by
  have hev : ∀ᶠ n in Filter.atTop, (m : ℕ∞) ≤ u n := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hlt : ((m - 1 : ℕ) : ℕ∞) < Filter.liminf u Filter.atTop := by
        rw [h]
        exact_mod_cast Nat.sub_lt hm one_pos
      have hE := Filter.eventually_lt_of_lt_liminf hlt
      filter_upwards [hE] with n hn
      rcases eq_or_ne (u n) ⊤ with h' | h'
      · rw [h']; exact le_top
      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h'
        rw [← hk] at hn ⊢
        have hk' : m - 1 < k := by exact_mod_cast hn
        have hmk : m ≤ k := by omega
        exact_mod_cast hmk
  refine ⟨hev, ?_⟩
  have hfr : ∃ᶠ n in Filter.atTop, u n ≤ (m : ℕ∞) := by
    by_contra hc
    rw [Filter.not_frequently] at hc
    have hev2 : ∀ᶠ n in Filter.atTop, ((m + 1 : ℕ) : ℕ∞) ≤ u n := by
      filter_upwards [hc] with n hn
      have hlt : (m : ℕ∞) < u n := lt_of_not_ge hn
      rcases eq_or_ne (u n) ⊤ with h' | h'
      · rw [h']; exact le_top
      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h'
        rw [← hk] at hlt ⊢
        have hk' : m < k := by exact_mod_cast hlt
        exact_mod_cast hk'
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ Filter.liminf u Filter.atTop := by
      rw [Filter.liminf_eq]
      exact le_sSup hev2
    rw [h] at hle
    have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
    omega
  exact (hfr.and_eventually hev).mono (fun n hn => le_antisymm hn.1 hn.2)

theorem nth_prime_strictMono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem nth_le (n : ℕ) : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
  nth_prime_strictMono (Nat.lt_succ_self n)

theorem gap_pos (n : ℕ) : 0 < gap n := by
  have := nth_le n
  simp only [gap]
  omega

theorem nth_prime_ge_three {n : ℕ} (hn : 1 ≤ n) : 3 ≤ Nat.nth Nat.Prime n := by
  have h := nth_prime_strictMono.monotone hn
  rwa [Nat.nth_prime_one_eq_three] at h

theorem gap_even {n : ℕ} (hn : 1 ≤ n) : Even (gap n) := by
  have h1 : Nat.Prime (Nat.nth Nat.Prime n) := Nat.prime_nth_prime n
  have h2 : Nat.Prime (Nat.nth Nat.Prime (n + 1)) := Nat.prime_nth_prime (n + 1)
  have h3 : 3 ≤ Nat.nth Nat.Prime n := nth_prime_ge_three hn
  have h4 : 3 ≤ Nat.nth Nat.Prime (n + 1) := nth_prime_ge_three (by omega)
  exact Nat.Odd.sub_odd (h2.odd_of_ne_two (by omega)) (h1.odd_of_ne_two (by omega))

theorem gap_frequently {m : ℕ}
    (hm : Filter.liminf (fun n => ((gap n : ℕ) : ℕ∞)) Filter.atTop = (m : ℕ∞)) :
    ∃ᶠ n in Filter.atTop, gap n = m := by
  have h := (liminf_attained (fun n => ((gap n : ℕ) : ℕ∞)) m hm).2
  exact h.mono (fun n hn => by exact_mod_cast hn)



noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => ((gap n : ℕ) : ℕ∞)) Filter.atTop

theorem ctrl_liminf :
    Filter.liminf (fun n : ℕ => if n % 2 = 0 then (3 : ℕ∞) else 5) Filter.atTop = 3 := by
  refine le_antisymm ?_ ?_
  · refine Filter.liminf_le_of_frequently_le' ?_
    refine Filter.frequently_atTop.mpr (fun a => ⟨2 * a, by omega, ?_⟩)
    simp [Nat.mul_mod_right]
  · rw [Filter.liminf_eq]
    refine le_sSup (Filter.Eventually.of_forall (fun n => ?_))
    split
    · exact le_refl _
    · decide

theorem ctrl_limsup :
    Filter.limsup (fun n : ℕ => if n % 2 = 0 then (3 : ℕ∞) else 5) Filter.atTop = 5 := by
  refine le_antisymm ?_ ?_
  · rw [Filter.limsup_eq]
    refine sInf_le (Filter.Eventually.of_forall (fun n => ?_))
    split
    · decide
    · exact le_refl _
  · refine Filter.le_limsup_of_frequently_le' ?_
    refine Filter.frequently_atTop.mpr (fun a => ⟨2 * a + 1, by omega, ?_⟩)
    have : (2 * a + 1) % 2 = 1 := by omega
    simp [this]

theorem part1 {m : ℕ} (hm : H1 = (m : ℕ∞)) : {n : ℕ | gap n = m}.Infinite :=
  Nat.frequently_atTop_iff_infinite.mp (gap_frequently hm)

theorem part2 {m : ℕ} (hm : H1 = (m : ℕ∞)) : 2 ≤ m ∧ Even m := by
  obtain ⟨n, hn1, hgap⟩ := Filter.frequently_atTop.mp (gap_frequently hm) 1
  have he : Even m := hgap ▸ gap_even hn1
  have hp : 0 < m := hgap ▸ gap_pos n
  rw [Nat.even_iff] at he
  exact ⟨by omega, Nat.even_iff.mpr he⟩

theorem part3 {m : ℕ} (hm : H1 = (m : ℕ∞)) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + m) := by
  obtain ⟨n, hn1, hgap⟩ := Filter.frequently_atTop.mp (gap_frequently hm) (N + 1)
  refine ⟨Nat.nth Nat.Prime n, ?_, Nat.prime_nth_prime n, ?_⟩
  · have h := nth_prime_strictMono.le_apply (x := n)
    omega
  · have hlt := nth_le n
    have heq : Nat.nth Nat.Prime n + m = Nat.nth Nat.Prime (n + 1) := by
      simp only [gap] at hgap; omega
    rw [heq]
    exact Nat.prime_nth_prime (n + 1)

theorem part4 {B : ℕ} (hB : H1 ≤ (B : ℕ∞)) :
    ∃ m : ℕ, 2 ≤ m ∧ m ≤ B ∧ Even m ∧ {n : ℕ | gap n = m}.Infinite ∧
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + m) := by
  have hne : H1 ≠ ⊤ := by
    intro h
    rw [h] at hB
    exact absurd hB (by simp)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hm' : H1 = (m : ℕ∞) := hm.symm
  have hmB : m ≤ B := by
    rw [hm'] at hB
    exact_mod_cast hB
  obtain ⟨h2, he⟩ := part2 hm'
  exact ⟨m, h2, hmB, he, part1 hm', fun N => part3 hm' N⟩

theorem proof :
  (∀ u : ℕ → ℕ∞, ∀ m : ℕ, Filter.liminf u Filter.atTop = (m : ℕ∞) →
      (∀ᶠ n in Filter.atTop, (m : ℕ∞) ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = (m : ℕ∞)))
  ∧ (∀ m : ℕ, Filter.liminf
        (fun n => ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℕ∞))
        Filter.atTop = (m : ℕ∞) →
      {n : ℕ | Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = m}.Infinite)
  ∧ (∀ m : ℕ, Filter.liminf
        (fun n => ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℕ∞))
        Filter.atTop = (m : ℕ∞) → 2 ≤ m ∧ Even m)
  ∧ (∀ m : ℕ, Filter.liminf
        (fun n => ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℕ∞))
        Filter.atTop = (m : ℕ∞) →
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + m))
  ∧ (∀ B : ℕ, Filter.liminf
        (fun n => ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℕ∞))
        Filter.atTop ≤ (B : ℕ∞) →
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ B ∧ Even m ∧
        {n : ℕ | Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = m}.Infinite ∧
        ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + m))
  ∧ (Filter.liminf (fun n : ℕ => if n % 2 = 0 then (3 : ℕ∞) else 5) Filter.atTop = 3
      ∧ Filter.limsup (fun n : ℕ => if n % 2 = 0 then (3 : ℕ∞) else 5) Filter.atTop = 5) :=
  ⟨liminf_attained,
   fun m hm => part1 hm,
   fun m hm => part2 hm,
   fun m hm => part3 hm,
   fun B hB => part4 hB,
   ⟨ctrl_liminf, ctrl_limsup⟩⟩

end Submissions.TwinPrimesH1Attained.LiminfAttained
