import Mathlib

/-! Every n >= 2 with n = 3 mod 5 admits an Erdos-Straus representation. -/

namespace Submissions.ErdosStrausThreeMod5.ThreeMod5

abbrev ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem key {n x y z : ℕ} (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) :
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h' : (4 : ℚ) * ((x : ℚ) * y * z) = (n : ℚ) * ((y : ℚ) * z + (x : ℚ) * z + (x : ℚ) * y) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h
  field_simp
  linear_combination h'

theorem split (n a b x y z : ℕ) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hay : a * y = n * x) (hbz : b * z = n * x) (hs : 4 * x = n + a + b) : ES n := by
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hnx : ((n : ℚ) * (x : ℚ)) ≠ 0 := mul_ne_zero hn' hx'
  have hay' : (a : ℚ) * (y : ℚ) = (n : ℚ) * (x : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hay
  have hbz' : (b : ℚ) * (z : ℚ) = (n : ℚ) * (x : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hbz
  have hs' : (4 : ℚ) * (x : ℚ) = (n : ℚ) + (a : ℚ) + (b : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hs
  have e1 : (1 : ℚ) / (y : ℚ) = (a : ℚ) / ((n : ℚ) * (x : ℚ)) := by
    rw [div_eq_div_iff hy' hnx]; linear_combination -hay'
  have e2 : (1 : ℚ) / (z : ℚ) = (b : ℚ) / ((n : ℚ) * (x : ℚ)) := by
    rw [div_eq_div_iff hz' hnx]; linear_combination -hbz'
  have e3 : (1 : ℚ) / (x : ℚ) = (n : ℚ) / ((n : ℚ) * (x : ℚ)) := by
    rw [div_eq_div_iff hx' hnx]; ring
  have hsum : (1 : ℚ) / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)
      = ((n : ℚ) + (a : ℚ) + (b : ℚ)) / ((n : ℚ) * (x : ℚ)) := by
    rw [e1, e2, e3]; ring
  rw [hsum, div_eq_div_iff hn' hnx]
  linear_combination (n : ℚ) * hs'

theorem es_even (m : ℕ) (hm : 0 < m) : ES (2 * m) :=
  ⟨m, m + 1, m * (m + 1), hm, Nat.succ_pos m, Nat.mul_pos hm (Nat.succ_pos m),
    key (by omega) hm (Nat.succ_pos m) (Nat.mul_pos hm (Nat.succ_pos m)) (by ring)⟩

theorem es_mod3 (k : ℕ) : ES (3 * k + 2) :=
  ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega,
    Nat.mul_pos (by omega) (by omega),
    key (by omega) (by omega) (by omega) (Nat.mul_pos (by omega) (by omega)) (by ring)⟩

theorem es_mod4 (k : ℕ) : ES (4 * k + 3) :=
  ⟨k + 1, (4 * k + 3) * (k + 1) + 1,
    ((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1),
    by omega, by omega,
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega),
    key (by omega) (by omega) (by omega)
      (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by ring)⟩

theorem es_mod8 (m : ℕ) : ES (8 * m + 5) :=
  ⟨2 * (m + 1), (8 * m + 5) * (m + 1), 2 * ((8 * m + 5) * (m + 1)),
    by omega, Nat.mul_pos (by omega) (by omega),
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega) (Nat.mul_pos (by omega) (by omega))
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

/-- `n ≡ 33 (mod 40)`: `4/n = 1/(10T) + 1/(5nT) + 1/(2nT)` with `T = (n+7)/40`. -/
theorem es_mod40 (t : ℕ) : ES (40 * t + 33) :=
  ⟨10 * (t + 1), 5 * ((40 * t + 33) * (t + 1)), 2 * ((40 * t + 33) * (t + 1)),
    by omega,
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega)
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

theorem es_three : ES 3 :=
  ⟨1, 4, 12, by norm_num, by norm_num, by norm_num,
    key (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

theorem es_mul {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) (h : ES d) : ES n := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk0 hx, Nat.mul_pos hk0 hy, Nat.mul_pos hk0 hz, ?_⟩
  push_cast
  rw [← div_div, hxyz]
  field_simp

theorem coverage : ∀ n : ℕ, 2 ≤ n → n % 24 ≠ 1 → ES n := by
  intro n hn h24
  by_cases h2 : n % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    exact es_even m (by omega)
  by_cases h3 : n % 3 = 2
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    exact es_mod3 k
  by_cases h3' : n % 3 = 0
  · exact es_mul (by omega) (Nat.dvd_of_mod_eq_zero h3') es_three
  by_cases h4 : n % 4 = 3
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    exact es_mod4 k
  by_cases h8 : n % 8 = 5
  · obtain ⟨m, rfl⟩ : ∃ m, n = 8 * m + 5 := ⟨n / 8, by omega⟩
    exact es_mod8 m
  · exact absurd (by omega : n % 24 = 1) h24

theorem threeModFive : ∀ n : ℕ, 2 ≤ n → n % 5 = 3 → ES n := by
  intro n hn h5
  by_cases h24 : n % 24 = 1
  · obtain ⟨t, rfl⟩ : ∃ t, n = 40 * t + 33 := ⟨n / 40, by omega⟩
    exact es_mod40 t
  · exact coverage n hn h24

theorem equiv :
    (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 → ES p) ↔ (∀ n : ℕ, 2 ≤ n → ES n) := by
  constructor
  · intro H n hn
    by_cases h5 : n % 5 = 3
    · exact threeModFive n hn h5
    by_cases h24 : n % 24 = 1
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
      by_cases hp24 : p % 24 = 1
      · by_cases hp5 : p % 5 = 3
        · exact es_mul (by omega) hpn (threeModFive p hp.two_le hp5)
        · exact es_mul (by omega) hpn (H p hp hp24 hp5)
      · exact es_mul (by omega) hpn (coverage p hp.two_le hp24)
    · exact coverage n hn h24
  · intro H p hp _ _
    exact H p hp.two_le

theorem proof : ∀ n : ℕ, 2 ≤ n → n % 5 = 3 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := threeModFive

end Submissions.ErdosStrausThreeMod5.ThreeMod5
