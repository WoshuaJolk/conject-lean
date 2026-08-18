import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
Proof of the Dirichlet barrier for the twin prime conjecture.

The engine is `runs`: given a modulus `q`, a reduced residue `a`, a shift `h ≥ 1` and a
depth `k`, it produces primes `p ≡ a (mod q)`, arbitrarily large, with `p + h, …, p + kh`
all composite.

Construction.  Two applications of Dirichlet's theorem.

1.  Pick a prime `s > max (k * h) q` with `s ≡ a (mod q)`.
2.  Put `L := ∏_{j ∈ [1,k]} (s + h * j)`.  Then `gcd (s, L) = 1`, because
    `gcd (s, s + h*j) = gcd (s, h*j)` and `s` is a prime exceeding `h*j > 0`; and
    `gcd (s, q) = 1` because `s` is a prime exceeding `q ≥ 1`.  Hence `gcd (s, q*L) = 1`.
3.  Pick a prime `p ≡ s (mod q*L)` with `p > max (max N L) s`.
4.  `q ∣ q*L` gives `p ≡ s ≡ a (mod q)`.  For `1 ≤ j ≤ k`, `(s + h*j) ∣ L ∣ q*L`, so
    `p + h*j ≡ s + h*j ≡ 0 (mod s + h*j)`; and `1 < s + h*j < p + h*j` since `s < p`.
    A number with a divisor strictly between `1` and itself is not prime.

The first conjunct is the case `h = 2`, `k = 1`.
-/

namespace Submissions.TwinPrimesDirichletBarrier.DirichletCertificate

/-- For every modulus `q`, every residue `a` coprime to `q`, every shift `h ≥ 1` and every
depth `k`, there are arbitrarily large primes `p ≡ a (mod q)` with `p + h, p + 2h, …, p + kh`
all composite. -/
theorem runs (q a h k N : ℕ) (hq : 0 < q) (hh : 0 < h) (hcop : Nat.Coprime a q) :
    ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p ≡ a [MOD q] ∧
      ∀ j : ℕ, 0 < j → j ≤ k → ¬ Nat.Prime (p + h * j) := by
  obtain ⟨s, hs_gt, hs_prime, hs_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (k * h) q) hq.ne' hcop
  have hsq : q < s := lt_of_le_of_lt (le_max_right (k * h) q) hs_gt
  have hskh : k * h < s := lt_of_le_of_lt (le_max_left (k * h) q) hs_gt
  have hs_cop_q : Nat.Coprime s q := by
    rw [Nat.Prime.coprime_iff_not_dvd hs_prime]
    intro hdvd
    exact absurd (Nat.le_of_dvd hq hdvd) (by omega)
  set L : ℕ := ∏ j ∈ Finset.Icc 1 k, (s + h * j) with hLdef
  have hLpos : 0 < L := Finset.prod_pos (fun j _ => by have := hs_prime.pos; omega)
  have hs_cop_L : Nat.Coprime s L := by
    apply Nat.Coprime.prod_right
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    have hlt : h * j < s := by
      have : h * j ≤ h * k := Nat.mul_le_mul_left h hjk
      have hkh : h * k = k * h := Nat.mul_comm h k
      omega
    have hco : Nat.Coprime s (h * j) := by
      rw [Nat.Prime.coprime_iff_not_dvd hs_prime]
      intro hdvd
      have := Nat.le_of_dvd (by positivity) hdvd
      omega
    have hcomm : s + h * j = h * j + s := by ring
    rw [hcomm, Nat.coprime_add_self_right]
    exact hco
  have hM : Nat.Coprime s (q * L) := Nat.Coprime.mul_right hs_cop_q hs_cop_L
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (max N L) s)
      (Nat.mul_ne_zero hq.ne' hLpos.ne') hM
  refine ⟨p, lt_of_le_of_lt (le_trans (le_max_left N L) (le_max_left _ s)) hp_gt,
    hp_prime, ?_, ?_⟩
  · exact (hp_mod.of_dvd ⟨L, rfl⟩).trans hs_mod
  · intro j hj0 hjk hprime
    have hdvdL : (s + h * j) ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hj0, hjk⟩)
    have hdvdM : (s + h * j) ∣ (q * L) := hdvdL.mul_left q
    have h1 : p ≡ s [MOD (s + h * j)] := hp_mod.of_dvd hdvdM
    have h2 : (s + h * j) ∣ (p + h * j) := by
      have hstep : p + h * j ≡ s + h * j [MOD (s + h * j)] := Nat.ModEq.add_right _ h1
      have h3 : (s + h * j) ≡ 0 [MOD (s + h * j)] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
      exact (Nat.modEq_zero_iff_dvd).mp (hstep.trans h3)
    have hslt : s < p := lt_of_le_of_lt (le_max_right (max N L) s) hp_gt
    have hhj : 0 < h * j := by positivity
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ h2) with hcase | hcase
    · have := hs_prime.two_le; omega
    · omega

/-- The barrier: the primes `p` with `p + 2` composite already meet every reduced residue
class modulo every modulus infinitely often, and the same failure occurs for every shift and
to every depth. -/
theorem proof :
  (∀ q a N : ℕ, 0 < q → Nat.Coprime a q →
      ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ ¬ Nat.Prime (p + 2) ∧ p ≡ a [MOD q])
  ∧ (∀ q a h k N : ℕ, 0 < q → 0 < h → Nat.Coprime a q →
      ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p ≡ a [MOD q] ∧
        ∀ j : ℕ, 0 < j → j ≤ k → ¬ Nat.Prime (p + h * j)) := by
  refine ⟨?_, fun q a h k N hq hh hcop => runs q a h k N hq hh hcop⟩
  intro q a N hq hcop
  obtain ⟨p, hpN, hpp, hpmod, hcomp⟩ := runs q a 2 1 N hq (by norm_num) hcop
  refine ⟨p, hpN, hpp, ?_, hpmod⟩
  have := hcomp 1 (by norm_num) (by norm_num)
  simpa using this

end Submissions.TwinPrimesDirichletBarrier.DirichletCertificate
