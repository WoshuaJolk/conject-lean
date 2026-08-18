import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
Two applications of Dirichlet's theorem and one product.

Given `H`, `q`, `a`, `N`:

1.  Take a prime `s` with `s > max (H.sup id) q` and `s ≡ a (mod q)`.
2.  Put `L := ∏_{h ∈ H} (s + h)`.  For `h ∈ H` we have `0 < h ≤ H.sup id < s`, so `s` is a
    prime not dividing `h`, hence `gcd (s, s + h) = gcd (s, h) = 1`; therefore
    `gcd (s, L) = 1`.  Also `s > q ≥ 1` and `s` prime give `gcd (s, q) = 1`, so
    `gcd (s, q * L) = 1`.
3.  Take a prime `p ≡ s (mod q * L)` with `p > max (max N L) s`.
4.  `q ∣ q * L` gives `p ≡ s ≡ a (mod q)`.  For `h ∈ H`, `(s + h) ∣ L ∣ q * L`, so
    `p + h ≡ s + h ≡ 0 (mod s + h)`; and `1 < s + h < p + h` because `s < p`.  A number with
    a divisor strictly between `1` and itself is not prime.
-/

namespace Submissions.TwinPrimesTupleBarrier.TupleCertificate

theorem proof :
    ∀ (H : Finset ℕ) (q a N : ℕ), 0 < q → Nat.Coprime a q → (∀ h ∈ H, 0 < h) →
      ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p ≡ a [MOD q] ∧ ∀ h ∈ H, ¬ Nat.Prime (p + h) := by
  intro H q a N hq hcop hpos
  obtain ⟨s, hs_gt, hs_prime, hs_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (H.sup id) q) hq.ne' hcop
  have hsq : q < s := lt_of_le_of_lt (le_max_right (H.sup id) q) hs_gt
  have hsH : ∀ h ∈ H, h < s := by
    intro h hh
    have h1 : h ≤ H.sup id := Finset.le_sup (f := id) hh
    have h2 : H.sup id < s := lt_of_le_of_lt (le_max_left (H.sup id) q) hs_gt
    omega
  have hs_cop_q : Nat.Coprime s q := by
    rw [Nat.Prime.coprime_iff_not_dvd hs_prime]
    intro hdvd
    exact absurd (Nat.le_of_dvd hq hdvd) (by omega)
  set L : ℕ := ∏ h ∈ H, (s + h) with hLdef
  have hLpos : 0 < L := Finset.prod_pos (fun h _ => by have := hs_prime.pos; omega)
  have hs_cop_L : Nat.Coprime s L := by
    apply Nat.Coprime.prod_right
    intro h hh
    have hhpos : 0 < h := hpos h hh
    have hhlt : h < s := hsH h hh
    have hco : Nat.Coprime s h := by
      rw [Nat.Prime.coprime_iff_not_dvd hs_prime]
      intro hdvd
      have := Nat.le_of_dvd hhpos hdvd
      omega
    have hcomm : s + h = h + s := by ring
    rw [hcomm, Nat.coprime_add_self_right]
    exact hco
  have hM : Nat.Coprime s (q * L) := Nat.Coprime.mul_right hs_cop_q hs_cop_L
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (max N L) s)
      (Nat.mul_ne_zero hq.ne' hLpos.ne') hM
  refine ⟨p, lt_of_le_of_lt (le_trans (le_max_left N L) (le_max_left _ s)) hp_gt,
    hp_prime, ?_, ?_⟩
  · exact (hp_mod.of_dvd ⟨L, rfl⟩).trans hs_mod
  · intro h hh hprime
    have hhpos : 0 < h := hpos h hh
    have hdvdL : (s + h) ∣ L := Finset.dvd_prod_of_mem _ hh
    have hdvdM : (s + h) ∣ (q * L) := hdvdL.mul_left q
    have h1 : p ≡ s [MOD (s + h)] := hp_mod.of_dvd hdvdM
    have h2 : (s + h) ∣ (p + h) := by
      have hstep : p + h ≡ s + h [MOD (s + h)] := Nat.ModEq.add_right _ h1
      have h3 : (s + h) ≡ 0 [MOD (s + h)] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
      exact (Nat.modEq_zero_iff_dvd).mp (hstep.trans h3)
    have hslt : s < p := lt_of_le_of_lt (le_max_right (max N L) s) hp_gt
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ h2) with hcase | hcase
    · have := hs_prime.two_le; omega
    · omega

end Submissions.TwinPrimesTupleBarrier.TupleCertificate
