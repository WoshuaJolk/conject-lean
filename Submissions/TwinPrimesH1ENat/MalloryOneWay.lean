import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

set_option maxRecDepth 100000

namespace Submissions.TwinPrimesH1ENat.MalloryOneWay

/-- The `n`-th prime gap. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁` in `ℕ∞`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- DELIBERATELY WEAKENED must-fail control.  Keeps the gap data and `2 ≤ H₁`, but gives only
ONE direction of the bridge - `twin primes → H₁ = 2` - dropping the converse, and drops the
two liminf-convention facts entirely.  True, kernel-checked, and strictly weaker than the
statement that was asked: the missing direction is the one that says the conjecture is
*equivalent* to `H₁ = 2` rather than merely implying it, and without it `H₁ = 2` could in
principle be strictly easier than the conjecture. -/
theorem proof :
  (gap 0 = 1 ∧ gap 1 = 2 ∧ gap 2 = 2 ∧ gap 3 = 4)
  ∧ 2 ≤ H1
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) → H1 = 2) := by
  have hmono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hlt : ∀ n : ℕ, Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    fun n => hmono (Nat.lt_succ_self n)
  have hgap2 : ∀ n : ℕ, 1 ≤ n → 2 ≤ gap n := by
    intro n hn
    have h1 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n := hmono.monotone hn
    rw [Nat.nth_prime_one_eq_three] at h1
    obtain ⟨a, ha⟩ := (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by
      have := hlt n; omega)
    have h2 := hlt n
    unfold gap
    omega
  have hodd : ∀ p : ℕ, Nat.Prime p → 2 < p → ¬ Nat.Prime (p + 1) := by
    intro p hp hp2 h1
    have h : Even (p + 1) := (hp.odd_of_ne_two (by omega)).add_one
    have := (Nat.Prime.even_iff h1).mp h
    omega
  have hH1ge : 2 ≤ H1 := by
    unfold H1
    rw [Filter.liminf_eq]
    refine le_sSup ?_
    refine Filter.eventually_atTop.mpr ⟨1, fun b hb => ?_⟩
    exact_mod_cast hgap2 b hb
  refine ⟨⟨by simp [gap], by simp [gap], by simp [gap], by simp [gap]⟩, hH1ge, ?_⟩
  intro tpc
  refine le_antisymm ?_ hH1ge
  have hfr : ∃ᶠ n in Filter.atTop, gap n = 2 := by
    refine Filter.frequently_atTop.mpr ?_
    intro M
    obtain ⟨p, hpN, hp, hp2⟩ := tpc (Nat.nth Nat.Prime M)
    have hM2 : 2 ≤ Nat.nth Nat.Prime M := by
      have := Nat.add_two_le_nth_prime M; omega
    have hpgt : 2 < p := by omega
    have hnp1 : ¬ Nat.Prime (p + 1) := hodd p hp hpgt
    have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have hc1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
      rw [Nat.count_succ]; simp [hp]
    have hc2 : Nat.count Nat.Prime (p + 2) = Nat.count Nat.Prime p + 1 := by
      have hpp : p + 2 = (p + 1) + 1 := rfl
      rw [hpp, Nat.count_succ, hc1]; simp [hnp1]
    have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = p + 2 := by
      rw [← hc2]; exact Nat.nth_count hp2
    refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
    · have hlt' : Nat.nth Nat.Prime M < Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
        rw [h1]; exact hpN
      exact le_of_lt ((Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hlt')
    · unfold gap
      rw [h1, h2]
      omega
  unfold H1
  rw [Filter.liminf_eq]
  refine sSup_le ?_
  intro a ha
  obtain ⟨n, hn1, hn2⟩ := (ha.and_frequently hfr).exists
  rw [hn2] at hn1
  simpa using hn1

end Submissions.TwinPrimesH1ENat.MalloryOneWay
