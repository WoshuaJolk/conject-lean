import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
Sundaram-type characterisation of twin prime pairs.

For `k ≥ 1` the pair `(6k − 1, 6k + 1)` consists of two primes exactly when `k` is not
represented by any of the four bilinear forms `6ab + a + b`, `6ab − a − b`, `6ab + a − b`,
`6ab − a + b` with `a, b ≥ 1`.

Mechanism.  `6k ± 1` is coprime to `6`, so every divisor is `≡ 1` or `≡ 5 (mod 6)`.  A
factorisation `6k + 1 = uv` therefore has `u ≡ v ≡ 1` or `u ≡ v ≡ 5`, giving
`(6a+1)(6b+1)` or `(6a−1)(6b−1)`, i.e. `k = 6ab + a + b` or `k = 6ab − a − b`.  A
factorisation `6k − 1 = uv` has one factor `≡ 1` and one `≡ 5`, giving `(6a+1)(6b−1)` or
`(6a−1)(6b+1)`, i.e. `k = 6ab − a + b` or `k = 6ab + a − b`.  Conversely each representation
exhibits a factorisation with both factors exceeding `1`.

All subtraction below is in `ℕ` and is guarded: every occurrence of `6a − 1` sits under
`a ≥ 1`, and the additive forms `k + a + b = 6ab` etc. are used in the statement precisely so
that no truncated subtraction appears there.
-/

namespace Submissions.TwinPrimesSundaram.SundaramSieve

/-- A divisor of a number coprime to `6` is congruent to `1` or `5` modulo `6`. -/
theorem res6 {n u : ℕ} (h2 : ¬ (2 ∣ n)) (h3 : ¬ (3 ∣ n)) (hu : u ∣ n) :
    u % 6 = 1 ∨ u % 6 = 5 := by
  have hlt : u % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hd2 : u % 2 = 0 → False := fun h => h2 (dvd_trans (Nat.dvd_of_mod_eq_zero h) hu)
  have hd3 : u % 3 = 0 → False := fun h => h3 (dvd_trans (Nat.dvd_of_mod_eq_zero h) hu)
  have hcases : u % 6 = 0 ∨ u % 6 = 1 ∨ u % 6 = 2 ∨ u % 6 = 3 ∨ u % 6 = 4 ∨ u % 6 = 5 := by
    omega
  rcases hcases with h | h | h | h | h | h
  · exact absurd (by omega : u % 2 = 0) hd2
  · exact Or.inl h
  · exact absurd (by omega : u % 2 = 0) hd2
  · exact absurd (by omega : u % 3 = 0) hd3
  · exact absurd (by omega : u % 2 = 0) hd2
  · exact Or.inr h

/-- Splitting a composite coprime to `6`: a factorisation with both factors at least `2`,
each congruent to `1` or `5` modulo `6`. -/
theorem split {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ Nat.Prime n)
    (h2 : ¬ (2 ∣ n)) (h3 : ¬ (3 ∣ n)) :
    ∃ u v : ℕ, n = u * v ∧ 2 ≤ u ∧ 2 ≤ v ∧
      (u % 6 = 1 ∨ u % 6 = 5) ∧ (v % 6 = 1 ∨ v % 6 = 5) := by
  obtain ⟨u, hudvd, hu2, hult⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
  obtain ⟨v, hv⟩ := hudvd
  have hvdvd : v ∣ n := ⟨u, by rw [hv]; ring⟩
  have hv2 : 2 ≤ v := by
    rcases Nat.lt_or_ge v 2 with h | h
    · interval_cases v <;> omega
    · exact h
  exact ⟨u, v, hv, hu2, hv2, res6 h2 h3 ⟨v, hv⟩, res6 h2 h3 hvdvd⟩

/-- The four bilinear forms of the Sundaram sieve, as a predicate on `k`. -/
abbrev Rep (k : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (k = 6*a*b + a + b ∨ k + a + b = 6*a*b ∨ k + b = 6*a*b + a ∨ k + a = 6*a*b + b)

theorem sundaram (k : ℕ) (hk : 0 < k) :
    (Nat.Prime (6*k - 1) ∧ Nat.Prime (6*k + 1)) ↔ ¬ Rep k := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
  have hminus : 6 * (j + 1) - 1 = 6 * j + 5 := by omega
  have hplus : 6 * (j + 1) + 1 = 6 * j + 7 := by omega
  rw [hminus, hplus]
  constructor
  · rintro ⟨hp5, hp7⟩ ⟨a, b, ha, hb, hrep⟩
    have hab : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have hba : b ≤ a * b := Nat.le_mul_of_pos_left b ha
    rcases hrep with h | h | h | h
    · refine (Nat.not_prime_mul (a := 6*a+1) (b := 6*b+1) (by omega) (by omega)) ?_
      have he : (6*a+1) * (6*b+1) = 36*(a*b) + 6*a + 6*b + 1 := by ring
      have : 6*a*b = 6*(a*b) := by ring
      rw [show (6*a+1)*(6*b+1) = 36*(a*b) + 6*a + 6*b + 1 from he] at *
      have hgoal : 36*(a*b) + 6*a + 6*b + 1 = 6*j + 7 := by omega
      rw [he, hgoal]; exact hp7
    · refine (Nat.not_prime_mul (a := 6*a-1) (b := 6*b-1) (by omega) (by omega)) ?_
      obtain ⟨a', rfl⟩ : ∃ a' : ℕ, a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b' : ℕ, b = b' + 1 := ⟨b - 1, by omega⟩
      have e1 : 6*(a'+1) - 1 = 6*a' + 5 := by omega
      have e2 : 6*(b'+1) - 1 = 6*b' + 5 := by omega
      have e3 : (6*a'+5) * (6*b'+5) = 36*(a'*b') + 30*a' + 30*b' + 25 := by ring
      have e4 : (a'+1)*(b'+1) = a'*b' + a' + b' + 1 := by ring
      have e5 : 6*(a'+1)*(b'+1) = 6*(a'*b') + 6*a' + 6*b' + 6 := by ring
      rw [e1, e2, e3]
      have hgoal : 36*(a'*b') + 30*a' + 30*b' + 25 = 6*j + 7 := by omega
      rw [hgoal]; exact hp7
    · refine (Nat.not_prime_mul (a := 6*b+1) (b := 6*a-1) (by omega) (by omega)) ?_
      obtain ⟨a', rfl⟩ : ∃ a' : ℕ, a = a' + 1 := ⟨a - 1, by omega⟩
      have e1 : 6*(a'+1) - 1 = 6*a' + 5 := by omega
      have e3 : (6*b+1) * (6*a'+5) = 36*(a'*b) + 30*b + 6*a' + 5 := by ring
      have e5 : 6*(a'+1)*b = 6*(a'*b) + 6*b := by ring
      rw [e1, e3]
      have hgoal : 36*(a'*b) + 30*b + 6*a' + 5 = 6*j + 5 := by omega
      rw [hgoal]; exact hp5
    · refine (Nat.not_prime_mul (a := 6*a+1) (b := 6*b-1) (by omega) (by omega)) ?_
      obtain ⟨b', rfl⟩ : ∃ b' : ℕ, b = b' + 1 := ⟨b - 1, by omega⟩
      have e1 : 6*(b'+1) - 1 = 6*b' + 5 := by omega
      have e3 : (6*a+1) * (6*b'+5) = 36*(a*b') + 30*a + 6*b' + 5 := by ring
      have e5 : 6*a*(b'+1) = 6*(a*b') + 6*a := by ring
      rw [e1, e3]
      have hgoal : 36*(a*b') + 30*a + 6*b' + 5 = 6*j + 5 := by omega
      rw [hgoal]; exact hp5
  · intro hnr
    constructor
    · by_contra hnp
      obtain ⟨u, v, huv, hu2, hv2, hu6, hv6⟩ :=
        split (n := 6*j+5) (by omega) hnp (by omega) (by omega)
      rcases hu6 with h1 | h1 <;> rcases hv6 with h2 | h2
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+1 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+1 := ⟨v/6, by omega⟩
        have e : (6*a+1)*(6*b+1) = 36*(a*b) + 6*a + 6*b + 1 := by ring
        rw [e] at huv; omega
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+1 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+5 := ⟨v/6, by omega⟩
        have e : (6*a+1)*(6*b+5) = 36*(a*b) + 30*a + 6*b + 5 := by ring
        rw [e] at huv
        refine hnr ⟨a, b+1, by omega, by omega, Or.inr (Or.inr (Or.inr ?_))⟩
        have e2 : 6*a*(b+1) = 6*(a*b) + 6*a := by ring
        omega
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+5 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+1 := ⟨v/6, by omega⟩
        have e : (6*a+5)*(6*b+1) = 36*(a*b) + 6*a + 30*b + 5 := by ring
        rw [e] at huv
        refine hnr ⟨b, a+1, by omega, by omega, Or.inr (Or.inr (Or.inr ?_))⟩
        have e2 : 6*b*(a+1) = 6*(a*b) + 6*b := by ring
        omega
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+5 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+5 := ⟨v/6, by omega⟩
        have e : (6*a+5)*(6*b+5) = 36*(a*b) + 30*a + 30*b + 25 := by ring
        rw [e] at huv; omega
    · by_contra hnp
      obtain ⟨u, v, huv, hu2, hv2, hu6, hv6⟩ :=
        split (n := 6*j+7) (by omega) hnp (by omega) (by omega)
      rcases hu6 with h1 | h1 <;> rcases hv6 with h2 | h2
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+1 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+1 := ⟨v/6, by omega⟩
        have e : (6*a+1)*(6*b+1) = 36*(a*b) + 6*a + 6*b + 1 := by ring
        rw [e] at huv
        refine hnr ⟨a, b, by omega, by omega, Or.inl ?_⟩
        have e2 : 6*a*b = 6*(a*b) := by ring
        omega
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+1 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+5 := ⟨v/6, by omega⟩
        have e : (6*a+1)*(6*b+5) = 36*(a*b) + 30*a + 6*b + 5 := by ring
        rw [e] at huv; omega
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+5 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+1 := ⟨v/6, by omega⟩
        have e : (6*a+5)*(6*b+1) = 36*(a*b) + 6*a + 30*b + 5 := by ring
        rw [e] at huv; omega
      · obtain ⟨a, rfl⟩ : ∃ a, u = 6*a+5 := ⟨u/6, by omega⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = 6*b+5 := ⟨v/6, by omega⟩
        have e : (6*a+5)*(6*b+5) = 36*(a*b) + 30*a + 30*b + 25 := by ring
        rw [e] at huv
        refine hnr ⟨a+1, b+1, by omega, by omega, Or.inr (Or.inl ?_)⟩
        have e2 : 6*(a+1)*(b+1) = 6*(a*b) + 6*a + 6*b + 6 := by ring
        omega

/-- Every twin prime pair beyond `(3,5)` has the shape `(6k−1, 6k+1)`. -/
theorem twin_form {p : ℕ} (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) (h3 : 3 < p) :
    ∃ k : ℕ, 0 < k ∧ p = 6*k - 1 ∧ p + 2 = 6*k + 1 := by
  have hnd2 : ¬ ((2 : ℕ) ∣ p) := by
    intro h
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h)
    omega
  have hnd3 : ¬ ((3 : ℕ) ∣ p) := by
    intro h
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 h)
    omega
  have h6 := res6 hnd2 hnd3 (dvd_refl p)
  rcases h6 with h | h
  · exfalso
    have hd : (3 : ℕ) ∣ (p + 2) := by omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp2 3 hd) with h1 | h1 <;> omega
  · exact ⟨(p + 1) / 6, by omega, by omega, by omega⟩

theorem proof :
  (∀ k : ℕ, 0 < k →
      ((Nat.Prime (6*k - 1) ∧ Nat.Prime (6*k + 1)) ↔
        ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
            (k = 6*a*b + a + b ∨ k + a + b = 6*a*b ∨
             k + b = 6*a*b + a ∨ k + a = 6*a*b + b)))
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
      ↔ (∀ N : ℕ, ∃ k : ℕ, N < k ∧ 0 < k ∧
            ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
                (k = 6*a*b + a + b ∨ k + a + b = 6*a*b ∨
                 k + b = 6*a*b + a ∨ k + a = 6*a*b + b))) := by
  refine ⟨sundaram, ?_, ?_⟩
  · intro h N
    obtain ⟨p, hpgt, hp1, hp2⟩ := h (6*N + 9)
    obtain ⟨k, hk, hkp, hkp2⟩ := twin_form hp1 hp2 (by omega)
    refine ⟨k, by omega, hk, ?_⟩
    have := (sundaram k hk).mp ⟨by rw [← hkp]; exact hp1, by rw [← hkp2]; exact hp2⟩
    exact this
  · intro h N
    obtain ⟨k, hkN, hk, hnr⟩ := h N
    obtain ⟨h1, h2⟩ := (sundaram k hk).mpr hnr
    exact ⟨6*k - 1, by omega, h1, by rw [show 6*k - 1 + 2 = 6*k + 1 by omega]; exact h2⟩

end Submissions.TwinPrimesSundaram.SundaramSieve
