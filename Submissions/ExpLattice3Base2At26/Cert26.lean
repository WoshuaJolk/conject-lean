import Mathlib

/-!
# A 26-vertex empty polytope in the exponential lattice `L₃(2)`
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Submissions.ExpLattice3Base2At26.Cert26

/-- An exponent triple; the lattice point is `(2 ^ a, 2 ^ b, 2 ^ c)`. -/
abbrev T := ℕ × ℕ × ℕ

/-- The value at the lattice point of `t` of the integer functional `a`. -/
def dt (a : ℤ × ℤ × ℤ) (t : T) : ℤ :=
  a.1 * 2 ^ t.1 + a.2.1 * 2 ^ t.2.1 + a.2.2 * 2 ^ t.2.2

/-- The 26 exponent triples of the certificate. -/
def EX : List T :=
  [(0, 8, 3),
   (1, 8, 3),
   (2, 7, 5),
   (3, 7, 5),
   (4, 8, 4),
   (5, 0, 6),
   (5, 1, 6),
   (5, 8, 4),
   (6, 5, 6),
   (6, 6, 6),
   (6, 8, 5),
   (7, 7, 6),
   (7, 9, 1),
   (7, 9, 2),
   (8, 4, 7),
   (8, 5, 7),
   (8, 9, 5),
   (9, 9, 7),
   (9, 10, 4),
   (9, 10, 5),
   (10, 9, 8),
   (10, 11, 0),
   (10, 11, 1),
   (11, 10, 9),
   (11, 11, 8),
   (12, 12, 9)]

/-- Convex-position certificates `(v, a, c)`: `⟪a, u⟫ ≤ c` for every other vertex `u`,
and `⟪a, v⟫ > c`. -/
def CP : List (T × (ℤ × ℤ × ℤ) × ℤ) :=
  [((0, 8, 3), ((-832), 411, 936), 111040),
   ((1, 8, 3), (568, (-351), (-2742)), (-111224)),
   ((2, 7, 5), ((-92), (-6), 33), (-448)),
   ((3, 7, 5), (56, (-64), (-303)), (-17664)),
   ((4, 8, 4), ((-787), 399, 1702), 114973),
   ((5, 0, 6), (145, (-192), (-815)), (-47904)),
   ((5, 1, 6), ((-219), 104, 641), 34120),
   ((5, 8, 4), (110, (-71), (-412)), (-21252)),
   ((6, 5, 6), (181, (-178), (-792)), (-45074)),
   ((6, 6, 6), ((-90), 47, 288), 15646),
   ((6, 8, 5), ((-355), 194, 1079), 61248),
   ((7, 7, 6), (72, (-47), (-267)), (-13984)),
   ((7, 9, 1), (1568, (-987), (-9600)), (-326336)),
   ((7, 9, 2), ((-110), 59, 192), 16530),
   ((8, 4, 7), (52, (-56), (-143)), (-6784)),
   ((8, 5, 7), ((-96), 48, 319), 17440),
   ((8, 9, 5), (635, (-397), (-2476)), (-120170)),
   ((9, 9, 7), ((-829), 489, 2655), 162304),
   ((9, 10, 4), (2892, (-1743), (-13664)), (-549568)),
   ((9, 10, 5), ((-373), 219, 1136), 68928),
   ((10, 9, 8), (32, (-28), (-81)), (-2624)),
   ((10, 11, 0), (923, (-503), (-4096)), (-93184)),
   ((10, 11, 1), ((-1059), 642, 3328), 233728),
   ((11, 10, 9), ((-822), 489, 2686), 173312),
   ((11, 11, 8), (136, (-74), (-543)), (-12831)),
   ((12, 12, 9), (103, (-24), (-520)), 55800)]

/-- Supporting halfspaces `(a, c)` of the hull: `⟪a, v⟫ ≤ c` for every vertex `v`.
Together they cut off every lattice point of the bounding box that is not a vertex. -/
def FAC : List ((ℤ × ℤ × ℤ) × ℤ) :=
  [(((-639), 381, 2048), 130048),
   (((-512), 269, 960), 76032),
   (((-256), 127, 0), 32256),
   (((-172), 101, 512), 31744),
   (((-153), 102, 512), 53248),
   (((-127), 64, 381), 20448),
   (((-84), 49, 256), 15360),
   (((-81), 48, 256), 15872),
   (((-64), 21, 120), 6272),
   (((-64), 37, 192), 11520),
   (((-45), 24, 148), 8192),
   (((-36), 21, 112), 6656),
   (((-31), 16, 96), 5184),
   (((-31), 16, 101), 5504),
   (((-20), 8, 49), 2512),
   (((-15), 8, 49), 2688),
   (((-13), 7, 42), 2304),
   (((-12), 7, 0), 2048),
   (((-8), 0, 7), 192),
   (((-3), 0, 14), 1024),
   (((-2), 0, 7), 384),
   (((-2), 3, 0), 4096),
   ((0, (-32), (-127)), (-8160)),
   ((0, (-3), (-128)), (-1792)),
   ((0, (-3), (-16)), (-896)),
   ((3, (-2), (-10)), (-512)),
   ((3, (-2), (-8)), 0),
   ((11, (-8), (-35)), (-1792)),
   ((11, (-7), (-40)), (-2048)),
   ((12, (-8), (-45)), (-2368)),
   ((14, (-9), (-52)), (-2688)),
   ((15, (-16), (-28)), 0),
   ((31, (-32), (-101)), (-5504)),
   ((32, (-21), (-120)), (-6272)),
   ((34, (-21), (-128)), (-6144)),
   ((64, (-41), (-240)), (-12288)),
   ((124, (-128), (-601)), (-34624)),
   ((172, (-101), (-1024)), (-31744)),
   ((255, (-127), (-1024)), 0),
   ((510, (-285), (-2048)), (-63488)),
   ((512, (-319), (-2016)), (-96768)),
   ((1664, (-1017), (-8448)), (-324608))]

/-- Every exponent triple in the box `{0, …, 12} × {0, …, 12} × {0, …, 9}`. -/
def BOX : List T :=
  (List.range 13).flatMap fun a => (List.range 13).flatMap fun b =>
    (List.range 10).map fun c => (a, b, c)

theorem cp_covers : ∀ t ∈ EX, t ∈ CP.map Prod.fst := by decide

theorem cp_ok : ∀ r ∈ CP,
    (∀ u ∈ EX, u ≠ r.1 → dt r.2.1 u ≤ r.2.2) ∧ r.2.2 < dt r.2.1 r.1 := by decide

theorem fac_ok : ∀ r ∈ FAC, ∀ u ∈ EX, dt r.1 u ≤ r.2 := by decide

theorem box_covered : ∀ t ∈ BOX, t ∈ EX ∨ ∃ r ∈ FAC, r.2 < dt r.1 t := by decide

theorem box_x : ∀ u ∈ EX, dt (1, 0, 0) u ≤ 4096 := by decide
theorem box_y : ∀ u ∈ EX, dt (0, 1, 0) u ≤ 4096 := by decide
theorem box_z : ∀ u ∈ EX, dt (0, 0, 1) u ≤ 512 := by decide

theorem card_ok : EX.toFinset.card = 26 := by decide

/-- The lattice point of `L₃(2)` with exponent triple `t`. -/
def rp (t : T) : Fin 3 → ℝ := ![2 ^ t.1, 2 ^ t.2.1, 2 ^ t.2.2]

/-- The real linear functional with integer coefficient triple `a`. -/
def LF (a : ℤ × ℤ × ℤ) (x : Fin 3 → ℝ) : ℝ :=
  (a.1 : ℝ) * x 0 + (a.2.1 : ℝ) * x 1 + (a.2.2 : ℝ) * x 2

/-- The vertex set. -/
def VS : Set (Fin 3 → ℝ) := rp '' (↑EX.toFinset : Set T)

/-- The exponential lattice `L₃(2)`. -/
def S3 : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n}

theorem LF_rp (a : ℤ × ℤ × ℤ) (t : T) : LF a (rp t) = (dt a t : ℝ) := by
  simp only [LF, rp, dt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  ring

theorem convex_LF (a : ℤ × ℤ × ℤ) (r : ℝ) : Convex ℝ {x : Fin 3 → ℝ | LF a x ≤ r} := by
  intro x hx y hy s u hs hu hsu
  simp only [Set.mem_setOf_eq, LF, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  have key : (a.1 : ℝ) * (s * x 0 + u * y 0) + (a.2.1 : ℝ) * (s * x 1 + u * y 1)
        + (a.2.2 : ℝ) * (s * x 2 + u * y 2)
      = s * ((a.1 : ℝ) * x 0 + (a.2.1 : ℝ) * x 1 + (a.2.2 : ℝ) * x 2)
        + u * ((a.1 : ℝ) * y 0 + (a.2.1 : ℝ) * y 1 + (a.2.2 : ℝ) * y 2) := by ring
  have hr : s * r + u * r = r := by rw [← add_mul, hsu, one_mul]
  rw [key]
  have h1 := mul_le_mul_of_nonneg_left hx hs
  have h2 := mul_le_mul_of_nonneg_left hy hu
  linarith

theorem hull_le {a : ℤ × ℤ × ℤ} {r : ℝ} {S : Set (Fin 3 → ℝ)}
    (hS : ∀ x ∈ S, LF a x ≤ r) {p : Fin 3 → ℝ} (hp : p ∈ convexHull ℝ S) : LF a p ≤ r :=
  convexHull_min hS (convex_LF a r) hp

theorem not_mem_hull {a : ℤ × ℤ × ℤ} {r : ℝ} {S : Set (Fin 3 → ℝ)}
    (hS : ∀ x ∈ S, LF a x ≤ r) {p : Fin 3 → ℝ} (hp : r < LF a p) :
    p ∉ convexHull ℝ S := fun h => absurd (hull_le hS h) (not_le.mpr hp)

theorem two_pow_inj {a b : ℕ} (h : (2 : ℝ) ^ a = 2 ^ b) : a = b := by
  have h' : ((2 ^ a : ℕ) : ℝ) = ((2 ^ b : ℕ) : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h')

theorem two_pow_le_lx {a : ℕ} (h : (2 : ℝ) ^ a ≤ 4096) : a ≤ 12 := by
  by_contra hc
  have hk : 12 + 1 ≤ a := by omega
  have hpow : (2 : ℝ) ^ (12 + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem two_pow_le_ly {a : ℕ} (h : (2 : ℝ) ^ a ≤ 4096) : a ≤ 12 := by
  by_contra hc
  have hk : 12 + 1 ≤ a := by omega
  have hpow : (2 : ℝ) ^ (12 + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem two_pow_le_lz {a : ℕ} (h : (2 : ℝ) ^ a ≤ 512) : a ≤ 9 := by
  by_contra hc
  have hk : 9 + 1 ≤ a := by omega
  have hpow : (2 : ℝ) ^ (9 + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem rp_injOn : Set.InjOn rp (↑EX.toFinset : Set T) := by
  intro s _ t _ h
  have h0 : (2 : ℝ) ^ s.1 = 2 ^ t.1 := by
    have := congrFun h 0; simpa [rp] using this
  have h1 : (2 : ℝ) ^ s.2.1 = 2 ^ t.2.1 := by
    have := congrFun h 1; simpa [rp] using this
  have h2 : (2 : ℝ) ^ s.2.2 = 2 ^ t.2.2 := by
    have := congrFun h 2; simpa [rp] using this
  have e0 := two_pow_inj h0
  have e1 := two_pow_inj h1
  have e2 := two_pow_inj h2
  obtain ⟨s1, s2, s3⟩ := s
  obtain ⟨t1, t2, t3⟩ := t
  simp_all

theorem mem_VS {t : T} (ht : t ∈ EX) : rp t ∈ VS := ⟨t, by simpa using ht, rfl⟩

theorem LF_le_of_mem {a : ℤ × ℤ × ℤ} {c : ℤ} (h : ∀ u ∈ EX, dt a u ≤ c) :
    ∀ x ∈ VS, LF a x ≤ (c : ℝ) := by
  rintro x ⟨t, ht, rfl⟩
  rw [LF_rp]
  exact_mod_cast h t (by simpa using ht)

theorem LF_le_of_mem_erase {a : ℤ × ℤ × ℤ} {c : ℤ} {v : T}
    (h : ∀ u ∈ EX, u ≠ v → dt a u ≤ c) : ∀ x ∈ VS \ {rp v}, LF a x ≤ (c : ℝ) := by
  rintro x ⟨⟨t, ht, rfl⟩, hne⟩
  rw [LF_rp]
  refine Int.cast_le.mpr (h t (by simpa using ht) ?_)
  rintro rfl
  exact hne rfl

theorem VS_finite : VS.Finite := (EX.toFinset.finite_toSet).image rp

theorem VS_ncard : VS.ncard = 26 := by
  rw [VS, Set.InjOn.ncard_image rp_injOn, Set.ncard_coe_finset, card_ok]

theorem VS_subset : VS ⊆ S3 := by
  rintro x ⟨t, -, rfl⟩ i
  fin_cases i
  · exact ⟨t.1, by simp [rp]⟩
  · exact ⟨t.2.1, by simp [rp]⟩
  · exact ⟨t.2.2, by simp [rp]⟩

theorem VS_convexPosition : ∀ v ∈ VS, v ∉ convexHull ℝ (VS \ {v}) := by
  rintro v ⟨t, ht, rfl⟩
  have htEX : t ∈ EX := by simpa using ht
  obtain ⟨r, hrCP, hr1⟩ := List.mem_map.mp (cp_covers t htEX)
  obtain ⟨hle, hgt⟩ := cp_ok r hrCP
  subst hr1
  exact not_mem_hull (LF_le_of_mem_erase hle) (by rw [LF_rp]; exact_mod_cast hgt)

theorem VS_empty : convexHull ℝ VS ∩ S3 ⊆ VS := by
  rintro p ⟨hp, hpS⟩
  obtain ⟨n0, hn0⟩ := hpS 0
  obtain ⟨n1, hn1⟩ := hpS 1
  obtain ⟨n2, hn2⟩ := hpS 2
  have hpe : p = rp (n0, n1, n2) := by
    funext i; fin_cases i <;> simp [rp, hn0, hn1, hn2]
  have bx0 : LF (1, 0, 0) p ≤ ((4096 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_x) hp
  have bx1 : LF (0, 1, 0) p ≤ ((4096 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_y) hp
  have bx2 : LF (0, 0, 1) p ≤ ((512 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_z) hp
  have e0 : n0 ≤ 12 := by
    refine two_pow_le_lx ?_
    rw [← hn0]; simpa [LF] using bx0
  have e1 : n1 ≤ 12 := by
    refine two_pow_le_ly ?_
    rw [← hn1]; simpa [LF] using bx1
  have e2 : n2 ≤ 9 := by
    refine two_pow_le_lz ?_
    rw [← hn2]; simpa [LF] using bx2
  have hbox : (n0, n1, n2) ∈ BOX := by
    simp only [BOX, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨n0, by omega, n1, by omega, n2, by omega, rfl⟩
  rcases box_covered _ hbox with hin | hcut
  · rw [hpe]; exact mem_VS hin
  · exfalso
    obtain ⟨r, hrFAC, hgt⟩ := hcut
    refine not_mem_hull (LF_le_of_mem (fac_ok r hrFAC)) ?_ hp
    rw [hpe, LF_rp]
    exact_mod_cast hgt

/-- **`h(L₃(2)) ≥ 26`.**  A 26-vertex empty polytope in `{2ⁿ : n ∈ ℕ₀}³`. -/
theorem proof :
    ∃ V : Set (Fin 3 → ℝ),
      (V.Finite ∧
        V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ∧
        (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
        convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ⊆ V) ∧
      V.ncard = 26 :=
  ⟨VS, ⟨VS_finite, VS_subset, VS_convexPosition, VS_empty⟩, VS_ncard⟩

end Submissions.ExpLattice3Base2At26.Cert26
