import Mathlib

/-! Erdos-Straus is equivalent to its restriction to shift-free primes p = 1 mod 24, p != 3 mod 5. -/

namespace Submissions.ErdosStrausShiftReduction.ShiftReduction

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


/-- **Oblath's criterion.** If `n+1 = d*e` with `e ≡ 3 (mod 4)` then, writing `e = 4F-1`,
`4/n = 1/(dF) + 1/(ndF) + 1/(nF)`. -/
theorem es_oblath (n d e : ℕ) (hn : 0 < n) (hde : n + 1 = d * e) (he : e % 4 = 3) : ES n := by
  obtain ⟨f, rfl⟩ : ∃ f, e = 4 * f + 3 := ⟨e / 4, by omega⟩
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hde)
  have hF : 0 < f + 1 := by omega
  have core : n + 1 + d = 4 * d * (f + 1) := by
    calc n + 1 + d = d * (4 * f + 3) + d := by rw [hde]
      _ = 4 * d * (f + 1) := by ring
  refine ⟨d * (f + 1), n * (d * (f + 1)), n * (f + 1),
    Nat.mul_pos hd hF, Nat.mul_pos hn (Nat.mul_pos hd hF), Nat.mul_pos hn hF,
    key hn (Nat.mul_pos hd hF) (Nat.mul_pos hn (Nat.mul_pos hd hF)) (Nat.mul_pos hn hF) ?_⟩
  calc 4 * (d * (f + 1) * (n * (d * (f + 1))) * (n * (f + 1)))
      = (n * n * d * (f + 1) * (f + 1)) * (4 * d * (f + 1)) := by ring
    _ = (n * n * d * (f + 1) * (f + 1)) * (n + 1 + d) := by rw [core]
    _ = n * (n * (d * (f + 1)) * (n * (f + 1)) + d * (f + 1) * (n * (f + 1))
          + d * (f + 1) * (n * (d * (f + 1)))) := by ring

theorem oblathAll : ∀ n : ℕ, 2 ≤ n → ∀ d e : ℕ, n + 1 = d * e → e % 4 = 3 → ES n :=
  fun n hn d e hde he => es_oblath n d e (by omega) hde he

theorem primeCase
    (H : ∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      (∀ e : ℕ, e ∣ (p + 1) → e % 4 ≠ 3) → ES p) :
    ∀ p : ℕ, p.Prime → ES p := by
  intro p hp
  by_cases hpob : ∃ e : ℕ, e ∣ (p + 1) ∧ e % 4 = 3
  · obtain ⟨e, ⟨d, hd⟩, he⟩ := hpob
    exact es_oblath p d e hp.pos (by rw [hd]; ring) he
  · by_cases hp5 : p % 5 = 3
    · exact threeModFive p hp.two_le hp5
    · by_cases hp24 : p % 24 = 1
      · exact H p hp hp24 hp5 (fun e hdvd he3 => hpob ⟨e, hdvd, he3⟩)
      · exact coverage p hp.two_le hp24

theorem sharp :
    (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      (∀ e : ℕ, e ∣ (p + 1) → e % 4 ≠ 3) → ES p) ↔ (∀ n : ℕ, 2 ≤ n → ES n) := by
  constructor
  · intro H n hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    exact es_mul (by omega) hpn (primeCase H p hp)
  · intro H p hp _ _ _
    exact H p hp.two_le

/-- **Shift criterion.** If `n + a = b*g` and `g + 1 = 4*a*m` then
`4/n = 1/(abm) + 1/(nbm) + 1/(nam)`. The case `a = 1` is Oblath's criterion. -/
theorem es_shift (n a b g m : ℕ) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hbg : n + a = b * g) (hg : g + 1 = 4 * a * m) : ES n := by
  have core : n + a + b = 4 * a * b * m := by
    calc n + a + b = b * g + b := by rw [hbg]
      _ = b * (g + 1) := by ring
      _ = b * (4 * a * m) := by rw [hg]
      _ = 4 * a * b * m := by ring
  have hx : 0 < a * b * m := Nat.mul_pos (Nat.mul_pos ha hb) hm
  have hy : 0 < n * b * m := Nat.mul_pos (Nat.mul_pos hn hb) hm
  have hz : 0 < n * a * m := Nat.mul_pos (Nat.mul_pos hn ha) hm
  refine ⟨a * b * m, n * b * m, n * a * m, hx, hy, hz, key hn hx hy hz ?_⟩
  calc 4 * (a * b * m * (n * b * m) * (n * a * m))
      = (n * n * a * b * m * m) * (4 * a * b * m) := by ring
    _ = (n * n * a * b * m * m) * (n + a + b) := by rw [core]
    _ = n * (n * b * m * (n * a * m) + a * b * m * (n * a * m)
          + a * b * m * (n * b * m)) := by ring

theorem shiftAll : ∀ n a b g m : ℕ, 2 ≤ n → 0 < a → 0 < b → 0 < m →
    n + a = b * g → g + 1 = 4 * a * m → ES n :=
  fun n a b g m hn ha hb hm hbg hg => es_shift n a b g m (by omega) ha hb hm hbg hg

theorem primeCase2
    (H : ∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      (∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m → p + a = b * g → g + 1 ≠ 4 * a * m) → ES p) :
    ∀ p : ℕ, p.Prime → ES p := by
  intro p hp
  by_cases hp5 : p % 5 = 3
  · exact threeModFive p hp.two_le hp5
  · by_cases hp24 : p % 24 = 1
    · by_cases hsh : ∃ a b g m : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧ p + a = b * g ∧ g + 1 = 4 * a * m
      · obtain ⟨a, b, g, m, ha, hb, hm, hbg, hg⟩ := hsh
        exact es_shift p a b g m hp.pos ha hb hm hbg hg
      · exact H p hp hp24 hp5
          (fun a b g m ha hb hm hbg hg => hsh ⟨a, b, g, m, ha, hb, hm, hbg, hg⟩)
    · exact coverage p hp.two_le hp24

theorem shiftReduction :
    (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
      (∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m → p + a = b * g → g + 1 ≠ 4 * a * m) → ES p)
    ↔ (∀ n : ℕ, 2 ≤ n → ES n) := by
  constructor
  · intro H n hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    exact es_mul (by omega) hpn (primeCase2 H p hp)
  · intro H p hp _ _ _
    exact H p hp.two_le

theorem proof :
    (∀ p : ℕ, p.Prime → p % 24 = 1 → p % 5 ≠ 3 →
        (∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m → p + a = b * g → g + 1 ≠ 4 * a * m) →
        ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
          (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      (∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
          (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) := shiftReduction

end Submissions.ErdosStrausShiftReduction.ShiftReduction
