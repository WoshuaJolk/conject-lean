import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.TwinPrimesNoLocalObstruction.LocalUnobstructed

/-- `{0,2}` is admissible at every prime: some residue class avoids both `0` and `-2`. -/
theorem admissible (p : ℕ) (hp : p.Prime) : ∃ a : ℕ, ¬ p ∣ a ∧ ¬ p ∣ (a + 2) := by
  by_cases h3 : p = 3
  · subst h3; exact ⟨2, by decide, by decide⟩
  · refine ⟨1, by simpa using hp.one_lt.ne', ?_⟩
    intro hc
    have h4 : p ∣ 3 := by simpa using hc
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h4)

/-- For every modulus `m ≥ 1` there are arbitrarily large `n` with `n` and `n+2` both
coprime to `m`.  Witness: `n ≡ -1 (mod m)`. -/
theorem locally_good (m : ℕ) (hm : 0 < m) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Nat.Coprime n m ∧ Nat.Coprime (n + 2) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨k + (k + 1) * (N + 1), by nlinarith, ?_, ?_⟩
  · have : Nat.Coprime (k + (k + 1) * (N + 1)) (k + 1) := by simp [Nat.Coprime]
    exact this
  · have he : k + (k + 1) * (N + 1) + 2 = 1 + (k + 1) * (N + 2) := by ring
    rw [he]
    have : Nat.Coprime (1 + (k + 1) * (N + 2)) (k + 1) := by simp [Nat.Coprime]
    exact this

/-- The triple `{0,2,4}` is inadmissible at `3`. -/
theorem three_dvd (a : ℕ) : 3 ∣ a * (a + 2) * (a + 4) := by
  have h : ∀ x : ZMod 3, x * (x + 2) * (x + 4) = 0 := by decide
  have h2 : ((a * (a + 2) * (a + 4) : ℕ) : ZMod 3) = 0 := by
    push_cast
    exact h (a : ZMod 3)
  exact (ZMod.natCast_eq_zero_iff _ _).mp h2

/-- Consequently `(3,5,7)` is the only prime triple of shape `(p, p+2, p+4)`. -/
theorem only_triple (p : ℕ) (h0 : p.Prime) (h2 : (p + 2).Prime) (h4 : (p + 4).Prime) :
    p = 3 := by
  have hd := three_dvd p
  have h3 : Nat.Prime 3 := by norm_num
  rcases (Nat.Prime.dvd_mul h3).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul h3).mp h with h' | h'
    · exact ((Nat.prime_dvd_prime_iff_eq h3 h0).mp h').symm
    · have : (3 : ℕ) = p + 2 := (Nat.prime_dvd_prime_iff_eq h3 h2).mp h'
      have := h0.two_le
      omega
  · have : (3 : ℕ) = p + 4 := (Nat.prime_dvd_prime_iff_eq h3 h4).mp h
    omega

theorem proof :
    (∀ p : ℕ, Nat.Prime p → ∃ a : ℕ, ¬ p ∣ a ∧ ¬ p ∣ (a + 2)) ∧
    (∀ m : ℕ, 0 < m → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Coprime n m ∧ Nat.Coprime (n + 2) m) ∧
    (∀ a : ℕ, 3 ∣ a * (a + 2) * (a + 4)) ∧
    (∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) → Nat.Prime (p + 4) → p = 3) :=
  ⟨admissible, locally_good, three_dvd, only_triple⟩

end Submissions.TwinPrimesNoLocalObstruction.LocalUnobstructed
