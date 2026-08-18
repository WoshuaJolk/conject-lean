import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

set_option maxRecDepth 100000

namespace Submissions.H1BoundedGapBridge.Bridge

noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The "two primes in a window of width `D`, infinitely often" predicate. -/
def PairForm (D : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n a b : ℕ, N < n ∧ a < b ∧ b ≤ D ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)

theorem hmono : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem hlt (n : ℕ) : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
  hmono (Nat.lt_succ_self n)

theorem hgap2 : ∀ n : ℕ, 1 ≤ n → 2 ≤ gap n := by
  intro n hn
  have h1 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n := hmono.monotone hn
  rw [Nat.nth_prime_one_eq_three] at h1
  obtain ⟨a, ha⟩ := (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
  obtain ⟨b, hb⟩ := (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by have := hlt n; omega)
  have h2 := hlt n
  unfold gap
  omega

theorem hH1ge : 2 ≤ H1 := by
  unfold H1
  rw [Filter.liminf_eq]
  refine le_sSup ?_
  refine Filter.eventually_atTop.mpr ⟨1, fun b hb => ?_⟩
  exact_mod_cast hgap2 b hb

/-- Frequently-small-gap form is what `H1 ≤ D` really says. -/
theorem freq_of_le {D : ℕ} (h : H1 ≤ (D : ℕ∞)) : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ gap m ≤ D := by
  intro M
  by_contra hcon
  push_neg at hcon
  have hev : ∀ᶠ n in Filter.atTop, ((D + 1 : ℕ) : ℕ∞) ≤ (gap n : ℕ∞) := by
    refine Filter.eventually_atTop.mpr ⟨M, fun b hb => ?_⟩
    have := hcon b hb
    exact_mod_cast this
  have h1 : ((D + 1 : ℕ) : ℕ∞) ≤ H1 := by
    unfold H1; rw [Filter.liminf_eq]; exact le_sSup hev
  have h2 : ((D + 1 : ℕ) : ℕ∞) ≤ (D : ℕ∞) := le_trans h1 h
  have : (D : ℕ) + 1 ≤ D := by exact_mod_cast h2
  omega

/-- If two primes lie within `D` of each other beyond every bound, some *consecutive* pair
of primes does too, arbitrarily far out. -/
theorem freq_of_pair {D : ℕ} (h : PairForm D) : ∃ᶠ m in Filter.atTop, gap m ≤ D := by
  refine Filter.frequently_atTop.mpr ?_
  intro M
  obtain ⟨n, a, b, hn, hab, hbD, hpa, hpb⟩ := h (Nat.nth Nat.Prime M)
  set p := n + a with hp
  set q := n + b with hq
  have hpq : p < q := by omega
  have hcp : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hpa
  have hstep : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    rw [Nat.count_succ]; simp [hpa]
  have hcq : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
    have := Nat.count_monotone Nat.Prime (show p + 1 ≤ q by omega)
    omega
  have hnq : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hpb
  have hnext : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≤ q := by
    rw [← hnq]; exact hmono.monotone hcq
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · have hlt' : Nat.nth Nat.Prime M < Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
      rw [hcp]; omega
    exact le_of_lt (hmono.lt_iff_lt.mp hlt')
  · unfold gap
    rw [hcp]
    omega

theorem le_of_pair {D : ℕ} (h : PairForm D) : H1 ≤ (D : ℕ∞) := by
  have hfr := freq_of_pair h
  unfold H1
  rw [Filter.liminf_eq]
  refine sSup_le ?_
  intro x hx
  obtain ⟨m, hm1, hm2⟩ := (hx.and_frequently hfr).exists
  exact le_trans hm1 (by exact_mod_cast hm2)

theorem pair_of_le {D : ℕ} (h : H1 ≤ (D : ℕ∞)) : PairForm D := by
  intro N
  obtain ⟨m, hm1, hm2⟩ := freq_of_le h (Nat.count Nat.Prime (N + 1))
  have hbig : N < Nat.nth Nat.Prime m := by
    have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime (N + 1)) ≤ Nat.nth Nat.Prime m :=
      hmono.monotone hm1
    have h2 : N + 1 ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (N + 1)) :=
      Nat.le_nth_count (fun hfin => absurd hfin (Set.Infinite.not_finite Nat.infinite_setOfPred_prime)) (N+1)
    omega
  refine ⟨Nat.nth Nat.Prime m, 0, gap m, hbig, ?_, hm2, ?_, ?_⟩
  · have := hlt m; unfold gap; omega
  · simpa using Nat.prime_nth_prime m
  · have := hlt m
    have : Nat.nth Nat.Prime m + gap m = Nat.nth Nat.Prime (m + 1) := by unfold gap; omega
    rw [this]; exact Nat.prime_nth_prime (m + 1)

theorem no_consecutive_primes (n : ℕ) (h2 : 2 < n) (h : Nat.Prime n) : ¬ Nat.Prime (n + 1) := by
  intro h1
  have : Even (n + 1) := (h.odd_of_ne_two (by omega)).add_one
  have := (Nat.Prime.even_iff h1).mp this
  omega

theorem proof :
    2 ≤ H1
    ∧ (∀ D : ℕ, H1 ≤ (D : ℕ∞) ↔
        ∀ N : ℕ, ∃ n a b : ℕ, N < n ∧ a < b ∧ b ≤ D ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b))
    ∧ (∀ (T : Finset ℕ) (D : ℕ), (∀ x ∈ T, x ≤ D) →
        (∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T, a < b ∧
            Nat.Prime (n + a) ∧ Nat.Prime (n + b)) →
        H1 ≤ (D : ℕ∞))
    ∧ (H1 ≤ 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    ∧ ((∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ ({0, 2} : Finset ℕ), ∃ b ∈ ({0, 2} : Finset ℕ),
          a < b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b))
        ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  refine ⟨hH1ge, fun D => ⟨fun h => pair_of_le h, fun h => le_of_pair h⟩, ?_, ?_, ?_⟩
  · intro T D hTD hDHL
    refine le_of_pair ?_
    intro N
    obtain ⟨n, hn, a, ha, b, hb, hab, hpa, hpb⟩ := hDHL N
    exact ⟨n, a, b, hn, hab, hTD b hb, hpa, hpb⟩
  · constructor
    · intro h N
      have h2 : H1 ≤ ((2 : ℕ) : ℕ∞) := by exact_mod_cast h
      obtain ⟨n, a, b, hn, hab, hbD, hpa, hpb⟩ := pair_of_le h2 (max N 2)
      have hnN : N < n := lt_of_le_of_lt (le_max_left N 2) hn
      have hn2 : 2 < n := lt_of_le_of_lt (le_max_right N 2) hn
      have hcases : (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hpb (no_consecutive_primes n hn2 (by simpa using hpa))
      · exact ⟨n, hnN, by simpa using hpa, by simpa using hpb⟩
      · have heq : n + 2 = (n + 1) + 1 := by omega
        rw [heq] at hpb
        exact absurd hpb (no_consecutive_primes (n + 1) (by omega) hpa)
    · intro h
      have : H1 ≤ ((2 : ℕ) : ℕ∞) := by
        refine le_of_pair ?_
        intro N
        obtain ⟨p, hpN, hp, hp2⟩ := h N
        exact ⟨p, 0, 2, hpN, by omega, le_refl 2, by simpa using hp, by simpa using hp2⟩
      exact_mod_cast this
  · constructor
    · intro h N
      obtain ⟨n, hn, a, ha, b, hb, hab, hpa, hpb⟩ := h N
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      have : a = 0 ∧ b = 2 := by omega
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨n, hn, by simpa using hpa, by simpa using hpb⟩
    · intro h N
      obtain ⟨p, hpN, hp, hp2⟩ := h N
      exact ⟨p, hpN, 0, by decide, 2, by decide, by omega, by simpa using hp, by simpa using hp2⟩

end Submissions.H1BoundedGapBridge.Bridge
