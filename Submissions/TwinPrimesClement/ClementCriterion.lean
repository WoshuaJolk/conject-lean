import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Prime.Basic

/-!
Clement's criterion, proved.  Everything is done in `ℕ`; `ZMod` appears only inside
`wilson_dvd`, which restates Mathlib's Wilson theorem as a divisibility.

Write `n = t + 1`, so `n - 1 = t` and `t` is even.  Put `X := 4 * (t ! + 1) + (t + 1)`.

* `t + 1` and `t + 3` are coprime (their gcd divides `2` and both are odd), so
  `(t+1)(t+3) ∣ X` iff `(t+1) ∣ X` and `(t+3) ∣ X`.
* `(t+1) ∣ X` iff `(t+1) ∣ 4(t! + 1)` iff `(t+1) ∣ t! + 1` (as `t+1` is odd, hence coprime
  to `4`) iff `t + 1` is prime, by Wilson.
* `X = (4·t! + 2) + (t + 3)`, so `(t+3) ∣ X` iff `(t+3) ∣ 2(2·t! + 1)` iff
  `(t+3) ∣ 2·t! + 1` (as `t+3` is odd).  And `(t+2)! + 1 = (2·t! + 1) + (t+3)·(t·t!)`,
  because `(t+2)(t+1) = t(t+3) + 2`, so `(t+3) ∣ (t+2)! + 1` iff `(t+3) ∣ 2·t! + 1`.
  By Wilson the left side says `t + 3` is prime.
-/

namespace Submissions.TwinPrimesClement.ClementCriterion

open Nat

/-- Wilson's theorem as a divisibility in `ℕ`. -/
theorem wilson_dvd {m : ℕ} (hm : 2 ≤ m) :
    Nat.Prime m ↔ m ∣ Nat.factorial (m - 1) + 1 := by
  have : NeZero m := ⟨by omega⟩
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega : m ≠ 1)]
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination h

/-- `k ∣ a + b` and `k ∣ b` together are equivalent to `k ∣ a`. -/
theorem dvd_add_cancel {k a b : ℕ} (hb : k ∣ b) : (k ∣ a + b) ↔ k ∣ a := by
  constructor
  · intro h; simpa using Nat.dvd_sub h hb
  · intro h; exact Nat.dvd_add h hb

theorem clement (n : ℕ) (h3 : 3 ≤ n) (hodd : Odd n) :
    (Nat.Prime n ∧ Nat.Prime (n + 2)) ↔
      n * (n + 2) ∣ 4 * (Nat.factorial (n - 1) + 1) + n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 1 := ⟨n - 1, by omega⟩
  have ht2 : 2 ≤ t := by omega
  have hteven : Even t := by
    rcases hodd with ⟨u, hu⟩
    exact ⟨u, by omega⟩
  obtain ⟨u, hu⟩ := hteven
  simp only [Nat.add_sub_cancel]
  -- coprimality of the two moduli
  have hcop2a : Nat.Coprime (t + 1) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hd; obtain ⟨v, hv⟩ := hd; omega
  have hcop2b : Nat.Coprime (t + 3) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hd; obtain ⟨v, hv⟩ := hd; omega
  have hcop4 : Nat.Coprime (t + 1) 4 := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_right 2 hcop2a
  have hcop : Nat.Coprime (t + 1) (t + 3) := by
    have hd2 : Nat.gcd (t + 1) (t + 3) ∣ 2 := by
      have h := Nat.dvd_sub (Nat.gcd_dvd_right (t + 1) (t + 3))
        (Nat.gcd_dvd_left (t + 1) (t + 3))
      simpa using h
    have hd1 := Nat.gcd_dvd_left (t + 1) (t + 3)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact h
    · exfalso
      rw [h] at hd1
      obtain ⟨v, hv⟩ := hd1
      omega
  -- the first modulus
  have hA : ((t + 1) ∣ 4 * (Nat.factorial t + 1) + (t + 1)) ↔ Nat.Prime (t + 1) := by
    rw [dvd_add_cancel (dvd_refl (t + 1))]
    rw [show 4 * (Nat.factorial t + 1) = (Nat.factorial t + 1) * 4 by ring]
    rw [Nat.Coprime.dvd_mul_right hcop4]
    rw [wilson_dvd (show 2 ≤ t + 1 by omega)]
    simp
  -- the second modulus
  have hrw : 4 * (Nat.factorial t + 1) + (t + 1) = (4 * Nat.factorial t + 2) + (t + 3) := by
    ring
  have hB : ((t + 3) ∣ 4 * (Nat.factorial t + 1) + (t + 1)) ↔ Nat.Prime (t + 3) := by
    rw [hrw, dvd_add_cancel (dvd_refl (t + 3))]
    rw [show 4 * Nat.factorial t + 2 = (2 * Nat.factorial t + 1) * 2 by ring]
    rw [Nat.Coprime.dvd_mul_right hcop2b]
    rw [wilson_dvd (show 2 ≤ t + 3 by omega)]
    have hfac : Nat.factorial (t + 3 - 1) + 1
        = (2 * Nat.factorial t + 1) + (t + 3) * (t * Nat.factorial t) := by
      have h1 : t + 3 - 1 = t + 2 := by omega
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [hfac, dvd_add_cancel (Dvd.intro _ rfl)]
  -- combine
  constructor
  · rintro ⟨hp1, hp2⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (hA.mpr hp1) (hB.mpr hp2)
  · intro h
    exact ⟨hA.mp (dvd_trans (dvd_mul_right (t + 1) (t + 3)) h),
           hB.mp (dvd_trans (dvd_mul_left (t + 3) (t + 1)) h)⟩

theorem proof :
  (∀ n : ℕ, 3 ≤ n → Odd n →
      ((Nat.Prime n ∧ Nat.Prime (n + 2)) ↔
        n * (n + 2) ∣ 4 * (Nat.factorial (n - 1) + 1) + n))
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
      ↔ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ 3 ≤ n ∧ Odd n ∧
            n * (n + 2) ∣ 4 * (Nat.factorial (n - 1) + 1) + n)) := by
  refine ⟨clement, ?_, ?_⟩
  · intro h N
    obtain ⟨p, hpN, hp1, hp2⟩ := h (max N 2)
    have hp2lt : 2 < p := lt_of_le_of_lt (le_max_right N 2) hpN
    have hpodd : Odd p := hp1.odd_of_ne_two (by omega)
    exact ⟨p, lt_of_le_of_lt (le_max_left N 2) hpN, by omega, hpodd,
      (clement p (by omega) hpodd).mp ⟨hp1, hp2⟩⟩
  · intro h N
    obtain ⟨n, hnN, hn3, hnodd, hdvd⟩ := h N
    obtain ⟨hp1, hp2⟩ := (clement n hn3 hnodd).mpr hdvd
    exact ⟨n, hnN, hp1, hp2⟩

end Submissions.TwinPrimesClement.ClementCriterion
