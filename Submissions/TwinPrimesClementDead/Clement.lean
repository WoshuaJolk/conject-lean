import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 10000

namespace Submissions.TwinPrimesClementDead.Clement

open Nat

/-- Clement's criterion (1949), and the elimination it certifies.

For every `n ≥ 2`, `n` and `n + 2` are both prime **iff** `n(n+2) ∣ 4((n−1)! + 1) + n`.
Consequently the twin prime conjecture is *equal to*, not merely implied by, the assertion
that this congruence has arbitrarily large solutions.

The proof is Wilson both ways.  Write `F = (n−1)!` and substitute `n = k + 2` so that no
truncated subtraction survives.  On the `n + 2 = k + 4` side, `(k+3)! = (k+3)(k+2)F` and
`(k+3)(k+2) = (k+4)(k+1) + 2`, so `2((k+3)! + 1) = (k+4)·2(k+1)F + (4F + 2)` while
`4(F + 1) + (k+2) = (4F + 2) + (k+4)`: the two divisibilities by `k+4` are the same
divisibility, namely `k + 4 ∣ 4F + 2`.  On the `n = k + 2` side the `+n` is absorbed
directly.  For the converse at `k+4`: if `k+4` is odd it is coprime to `2` and Wilson
applies; if `k+4 = 2t` is even then `t ∣ (k+3)! + 1` and `t ∣ (k+3)!` since `2 ≤ t ≤ k+3`,
forcing `t = 1` and contradicting `k + 4 ≥ 4`.  That is the step which would otherwise need
"`m` composite and `m > 4` implies `m ∣ (m−1)!`", and it avoids it. -/
theorem proof :
    (∀ n : ℕ, 2 ≤ n →
        ((Nat.Prime n ∧ Nat.Prime (n + 2)) ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n))
    ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
        ↔ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ 2 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n))
    ∧ (3 * 5 ∣ 4 * ((3 - 1)! + 1) + 3)
    ∧ (11 * 13 ∣ 4 * ((11 - 1)! + 1) + 11)
    ∧ ¬ (7 * 9 ∣ 4 * ((7 - 1)! + 1) + 7)
    ∧ ¬ (9 * 11 ∣ 4 * ((9 - 1)! + 1) + 9) := by
  have wilson_dvd : ∀ n : ℕ, n ≠ 1 → (Nat.Prime n ↔ n ∣ (n - 1)! + 1) := by
    intro n hn
    rw [Nat.prime_iff_fac_equiv_neg_one hn, ← ZMod.natCast_eq_zero_iff]
    push_cast
    exact (add_eq_zero_iff_eq_neg).symm

  have clement : ∀ n : ℕ, 2 ≤ n →
      ((Nat.Prime n ∧ Nat.Prime (n + 2)) ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hs : k + 2 - 1 = k + 1 := rfl
    have h4 : k + 2 + 2 = k + 4 := by ring
    rw [hs, h4]
    have addself : ∀ (m A : ℕ), (m ∣ A + m ↔ m ∣ A) := by
      intro m A
      constructor
      · intro h; simpa using Nat.dvd_sub h (dvd_refl m)
      · intro h; exact dvd_add h (dvd_refl m)
    have hfac : (k + 3)! = (k + 3) * (k + 2) * (k + 1)! := by
      have h1 : (k + 2 + 1)! = (k + 2 + 1) * (k + 2)! := Nat.factorial_succ (k + 2)
      have h2 : (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := Nat.factorial_succ (k + 1)
      have e1 : k + 2 + 1 = k + 3 := by ring
      have e2 : k + 1 + 1 = k + 2 := by ring
      rw [e1] at h1; rw [e2] at h2
      rw [h1, h2]; ring
    have red1 : (k + 2) ∣ 4 * ((k + 1)! + 1) + (k + 2) ↔ (k + 2) ∣ 4 * ((k + 1)! + 1) :=
      addself (k + 2) (4 * ((k + 1)! + 1))
    have red2 : (k + 4) ∣ 4 * ((k + 1)! + 1) + (k + 2) ↔ (k + 4) ∣ 2 * ((k + 3)! + 1) := by
      have e1 : 4 * ((k + 1)! + 1) + (k + 2) = (4 * (k + 1)! + 2) + (k + 4) := by ring
      have e2 : 2 * ((k + 3)! + 1) = (k + 4) * (2 * (k + 1) * (k + 1)!) + (4 * (k + 1)! + 2) := by
        rw [hfac]; ring
      rw [e1, e2]
      constructor
      · intro h
        exact dvd_add (Dvd.intro _ rfl) ((addself (k + 4) (4 * (k + 1)! + 2)).mp h)
      · intro h
        exact (addself (k + 4) (4 * (k + 1)! + 2)).mpr
          ((Nat.dvd_add_right (Dvd.intro _ rfl)).mp h)
    have wil2 : Nat.Prime (k + 2) ↔ (k + 2) ∣ (k + 1)! + 1 := by
      have := wilson_dvd (k + 2) (by omega); rwa [hs] at this
    have wil4 : Nat.Prime (k + 4) ↔ (k + 4) ∣ (k + 3)! + 1 := by
      have := wilson_dvd (k + 4) (by omega)
      have e : k + 4 - 1 = k + 3 := rfl
      rwa [e] at this
    constructor
    · rintro ⟨hp, hq⟩
      have hk0 : k ≠ 0 := by rintro rfl; exact absurd hq (by decide)
      have hodd : ¬ (2 ∣ k + 2) := by
        intro h2
        have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2).resolve_left (by omega)
        omega
      have hcop : Nat.Coprime (k + 2) (k + 4) := by
        have h1 : Nat.gcd (k + 2) (k + 4) ∣ 2 := by
          have := Nat.dvd_sub (Nat.gcd_dvd_right (k + 2) (k + 4)) (Nat.gcd_dvd_left (k + 2) (k + 4))
          simpa using this
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · exact absurd (dvd_trans (dvd_of_eq h.symm) (Nat.gcd_dvd_left (k + 2) (k + 4))) hodd
      refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
      · exact red1.mpr (Dvd.dvd.mul_left (wil2.mp hp) 4)
      · exact red2.mpr (Dvd.dvd.mul_left (wil4.mp hq) 2)
    · intro hdvd
      have hd2 : (k + 4) ∣ 4 * ((k + 1)! + 1) + (k + 2) :=
        dvd_trans (dvd_mul_left (k + 4) (k + 2)) hdvd
      have hd1 : (k + 2) ∣ 4 * ((k + 1)! + 1) + (k + 2) :=
        dvd_trans (dvd_mul_right (k + 2) (k + 4)) hdvd
      have hq : Nat.Prime (k + 4) := by
        by_cases he : 2 ∣ k + 4
        · exfalso
          obtain ⟨t, ht⟩ := he
          have ht2 : 2 ≤ t := by omega
          have h2 : (2 * t) ∣ 2 * ((k + 3)! + 1) := by rw [← ht]; exact red2.mp hd2
          have h3 : t ∣ (k + 3)! + 1 := (mul_dvd_mul_iff_left (a := 2) (by norm_num)).mp h2
          have h5 : t ∣ 1 := (Nat.dvd_add_right (Nat.dvd_factorial (by omega) (by omega))).mp h3
          have := Nat.le_of_dvd Nat.one_pos h5
          omega
        · have hcop : Nat.Coprime (k + 4) 2 :=
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr he).symm
          refine wil4.mpr (hcop.dvd_of_dvd_mul_left ?_)
          simpa [mul_comm] using red2.mp hd2
      have hodd : ¬ (2 ∣ k + 2) := by
        intro h2
        have he : (2 : ℕ) ∣ k + 4 := by omega
        have := (Nat.Prime.eq_one_or_self_of_dvd hq 2 he).resolve_left (by omega)
        omega
      have hcop4 : Nat.Coprime (k + 2) 4 := by
        have h2 : Nat.Coprime (k + 2) 2 :=
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
        have e : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [e]
        exact Nat.Coprime.pow_right 2 h2
      have hp : Nat.Prime (k + 2) := by
        refine wil2.mpr (hcop4.dvd_of_dvd_mul_left ?_)
        simpa [mul_comm] using red1.mp hd1
      exact ⟨hp, hq⟩
  refine ⟨clement, ⟨?_, ?_⟩, by decide, by decide, by decide, by decide⟩
  · intro tpc N
    obtain ⟨p, hpN, hp, hp2⟩ := tpc N
    exact ⟨p, hpN, hp.two_le, (clement p hp.two_le).mp ⟨hp, hp2⟩⟩
  · intro cle N
    obtain ⟨n, hnN, hn2, hdvd⟩ := cle N
    obtain ⟨hp, hp2⟩ := (clement n hn2).mpr hdvd
    exact ⟨n, hnN, hp, hp2⟩

end Submissions.TwinPrimesClementDead.Clement
