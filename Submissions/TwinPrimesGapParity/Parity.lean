import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting

namespace Submissions.TwinPrimesGapParity.Parity

/-- Every difference of two primes above `2` is even and at least `2`; the same for the
successive differences of `Nat.nth Nat.Prime` from index `1` on; and the two exceptional
data points at indices `0` and `2`.

The pair form is the whole content: past `2` a prime is odd, so `p = 2a + 1`, `q = 2b + 1`
and `q - p = 2(b - a)`, positive because `p < q`.  The indexed form is that applied to
`Nat.nth Nat.Prime n` and `Nat.nth Nat.Prime (n + 1)`, which are prime by
`Nat.prime_nth_prime` and strictly ordered by `Nat.nth_strictMono` applied to Euclid's
theorem in the form `Nat.infinite_setOfPred_prime`; the hypothesis `2 < Nat.nth Nat.Prime n`
for `n ≥ 1` comes from monotonicity and `Nat.nth Nat.Prime 1 = 3`. -/
theorem proof :
  (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → p < q → 2 ≤ q - p ∧ Even (q - p))
  ∧ (∀ n : ℕ, Nat.Prime (Nat.nth Nat.Prime n))
  ∧ (∀ n : ℕ, Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1))
  ∧ (∀ n : ℕ, 1 ≤ n →
        2 ≤ Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n
      ∧ Even (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n))
  ∧ (Nat.nth Nat.Prime 0 = 2 ∧ Nat.nth Nat.Prime 1 = 3
      ∧ Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0 = 1
      ∧ ¬ Even (Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0))
  ∧ (Nat.nth Nat.Prime 2 = 5 ∧ Nat.nth Nat.Prime 3 = 7
      ∧ Nat.nth Nat.Prime 3 - Nat.nth Nat.Prime 2 = 2) := by
  have key : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → p < q →
      2 ≤ q - p ∧ Even (q - p) := by
    intro p q hp hq hp2 hpq
    obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := hq.odd_of_ne_two (by omega)
    subst ha
    subst hb
    refine ⟨by omega, ?_⟩
    have h : 2 * b + 1 - (2 * a + 1) = 2 * (b - a) := by omega
    rw [h]
    exact even_two_mul _
  have hmono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime
  refine ⟨key, Nat.prime_nth_prime, fun n => hmono (Nat.lt_succ_self n), ?_, ?_, ?_⟩
  · intro n hn
    have h1 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n := hmono.monotone hn
    rw [Nat.nth_prime_one_eq_three] at h1
    exact key _ _ (Nat.prime_nth_prime n) (Nat.prime_nth_prime (n + 1)) (by omega)
      (hmono (Nat.lt_succ_self n))
  · refine ⟨Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, ?_, ?_⟩
    · rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
    · rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
      decide
  · refine ⟨Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, ?_⟩
    rw [Nat.nth_prime_three_eq_seven, Nat.nth_prime_two_eq_five]

end Submissions.TwinPrimesGapParity.Parity
