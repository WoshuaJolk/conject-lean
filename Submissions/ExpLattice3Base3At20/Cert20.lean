import Mathlib

/-!
# A 20-vertex empty polytope in the exponential lattice `L₃(3)`
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Submissions.ExpLattice3Base3At20.Cert20

/-- An exponent triple; the lattice point is `(2 ^ a, 2 ^ b, 2 ^ c)`. -/
abbrev T := ℕ × ℕ × ℕ

/-- The value at the lattice point of `t` of the integer functional `a`. -/
def dt (a : ℤ × ℤ × ℤ) (t : T) : ℤ :=
  a.1 * 3 ^ t.1 + a.2.1 * 3 ^ t.2.1 + a.2.2 * 3 ^ t.2.2

/-- The 20 exponent triples of the certificate. -/
def EX : List T :=
  [(0, 7, 3),
   (0, 9, 7),
   (1, 7, 3),
   (1, 9, 7),
   (3, 7, 4),
   (4, 6, 0),
   (4, 6, 1),
   (4, 8, 6),
   (5, 0, 1),
   (5, 1, 1),
   (5, 3, 2),
   (5, 5, 3),
   (5, 6, 4),
   (7, 7, 7),
   (8, 7, 8),
   (8, 10, 9),
   (9, 11, 10),
   (11, 6, 11),
   (12, 5, 12),
   (12, 6, 12)]

/-- Convex-position certificates `(v, a, c)`: `⟪a, u⟫ ≤ c` for every other vertex `u`,
and `⟪a, v⟫ > c`. -/
def CP : List (T × (ℤ × ℤ × ℤ) × ℤ) :=
  [((0, 7, 3), ((-9477), (-559), 3402), (-1159110)),
   ((0, 9, 7), ((-37179), (-2317), 19041), (-4074381)),
   ((1, 7, 3), (3775, 534, (-7981)), 956146),
   ((1, 9, 7), (10712169, 2396444, (-10670844)), 23842783593),
   ((3, 7, 4), ((-17172), (-1066), 8451), (-2120337)),
   ((4, 6, 0), ((-638), (-17), (-4551)), (-77724)),
   ((4, 6, 1), ((-1829), (-163), 927), (-266049)),
   ((4, 8, 6), ((-1071), (-68), 553), (-130104)),
   ((5, 0, 1), (7849, (-486), (-7896)), 1882161),
   ((5, 1, 1), (187510, 9938, (-190825)), 45002393),
   ((5, 3, 2), ((-34519), (-7812), 34479), (-8292492)),
   ((5, 5, 3), (111653, 11298, (-111646)), 26830635),
   ((5, 6, 4), (6363, 797, (-6453)), 1593729),
   ((7, 7, 7), (681, 85, (-687)), 172629),
   ((8, 7, 8), (531425, 66286, (-531241)), 146107638),
   ((8, 10, 9), ((-112238), (-14325), 79590), (-19295433)),
   ((9, 11, 10), (9633360, 2261169, (-9595427)), 23550290658),
   ((11, 6, 11), ((-51037), (-11862), 51017), (-12260802)),
   ((12, 5, 12), (60746, (-6561), (-60710)), 14572587),
   ((12, 6, 12), (10898847, 2406024, (-10857158)), 23645862387)]

/-- Supporting halfspaces `(a, c)` of the hull: `⟪a, v⟫ ≤ c` for every vertex `v`.
Together they cut off every lattice point of the bounding box that is not a vertex. -/
def FAC : List ((ℤ × ℤ × ℤ) × ℤ) :=
  [(((-59049), (-3760), 30600), (-7144929)),
   (((-30604), (-6921), 30591), (-7348320)),
   (((-14747), (-3645), 14742), (-3542940)),
   (((-9840), (-2187), 9841), 0),
   (((-6561), (-412), 3159), (-822312)),
   (((-6561), (-403), 3267), (-793881)),
   (((-6561), (-364), 3279), 0),
   (((-3228), (-729), 3227), (-708588)),
   (((-2458), (-567), 2457), (-590490)),
   (((-2187), (-130), 1053), (-258066)),
   (((-1863), (-121), 972), (-236196)),
   (((-1093), (-243), 1080), (-262440)),
   (((-729), (-40), 0), (-88209)),
   (((-364), (-81), 0), (-88533)),
   (((-364), (-81), 351), (-87480)),
   (((-12), 0, 13), 531441),
   ((0, 10, (-81)), 19683),
   ((0, 13, (-729)), 8748),
   ((0, 13, (-36)), 177147),
   ((1, 0, (-81)), 0),
   ((9, 1, (-9)), 2187),
   ((81, 10, (-100)), 19413),
   ((81, 10, (-90)), 19683),
   ((454, 91, (-3741)), 99372),
   ((729, 91, (-729)), 199017),
   ((3159, 400, (-3240)), 796797),
   ((9477, 1183, (-9567)), 2390391),
   ((13081, 1440, (-13077)), 3175524),
   ((88573, 0, (-88533)), 21257640),
   ((98401, 9837, (-98370)), 23645844),
   ((1049031, 131040, (-1048667)), 288972684),
   ((9649773, 2263707, (-9608524)), 23571652212)]

/-- Every exponent triple in the box `{0, …, 12} × {0, …, 11} × {0, …, 12}`. -/
def BOX : List T :=
  (List.range 13).flatMap fun a => (List.range 12).flatMap fun b =>
    (List.range 13).map fun c => (a, b, c)

theorem cp_covers : ∀ t ∈ EX, t ∈ CP.map Prod.fst := by decide

theorem cp_ok : ∀ r ∈ CP,
    (∀ u ∈ EX, u ≠ r.1 → dt r.2.1 u ≤ r.2.2) ∧ r.2.2 < dt r.2.1 r.1 := by decide

theorem fac_ok : ∀ r ∈ FAC, ∀ u ∈ EX, dt r.1 u ≤ r.2 := by decide

theorem box_covered : ∀ t ∈ BOX, t ∈ EX ∨ ∃ r ∈ FAC, r.2 < dt r.1 t := by decide

theorem box_x : ∀ u ∈ EX, dt (1, 0, 0) u ≤ 531441 := by decide
theorem box_y : ∀ u ∈ EX, dt (0, 1, 0) u ≤ 177147 := by decide
theorem box_z : ∀ u ∈ EX, dt (0, 0, 1) u ≤ 531441 := by decide

theorem card_ok : EX.toFinset.card = 20 := by decide

/-- The lattice point of `L₃(2)` with exponent triple `t`. -/
def rp (t : T) : Fin 3 → ℝ := ![3 ^ t.1, 3 ^ t.2.1, 3 ^ t.2.2]

/-- The real linear functional with integer coefficient triple `a`. -/
def LF (a : ℤ × ℤ × ℤ) (x : Fin 3 → ℝ) : ℝ :=
  (a.1 : ℝ) * x 0 + (a.2.1 : ℝ) * x 1 + (a.2.2 : ℝ) * x 2

/-- The vertex set. -/
def VS : Set (Fin 3 → ℝ) := rp '' (↑EX.toFinset : Set T)

/-- The exponential lattice `L₃(2)`. -/
def S3 : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (3 : ℝ) ^ n}

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

theorem two_pow_inj {a b : ℕ} (h : (3 : ℝ) ^ a = (3 : ℝ) ^ b) : a = b := by
  have h' : ((3 ^ a : ℕ) : ℝ) = ((3 ^ b : ℕ) : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (by norm_num) (Nat.cast_injective h')

theorem two_pow_le_lx {a : ℕ} (h : (3 : ℝ) ^ a ≤ 531441) : a ≤ 12 := by
  by_contra hc
  have hk : 12 + 1 ≤ a := by omega
  have hpow : (3 : ℝ) ^ (12 + 1) ≤ (3 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem two_pow_le_ly {a : ℕ} (h : (3 : ℝ) ^ a ≤ 177147) : a ≤ 11 := by
  by_contra hc
  have hk : 11 + 1 ≤ a := by omega
  have hpow : (3 : ℝ) ^ (11 + 1) ≤ (3 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem two_pow_le_lz {a : ℕ} (h : (3 : ℝ) ^ a ≤ 531441) : a ≤ 12 := by
  by_contra hc
  have hk : 12 + 1 ≤ a := by omega
  have hpow : (3 : ℝ) ^ (12 + 1) ≤ (3 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem rp_injOn : Set.InjOn rp (↑EX.toFinset : Set T) := by
  intro s _ t _ h
  have h0 : (3 : ℝ) ^ s.1 = (3 : ℝ) ^ t.1 := by
    have := congrFun h 0; simpa [rp] using this
  have h1 : (3 : ℝ) ^ s.2.1 = (3 : ℝ) ^ t.2.1 := by
    have := congrFun h 1; simpa [rp] using this
  have h2 : (3 : ℝ) ^ s.2.2 = (3 : ℝ) ^ t.2.2 := by
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

theorem VS_ncard : VS.ncard = 20 := by
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
  have bx0 : LF (1, 0, 0) p ≤ ((531441 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_x) hp
  have bx1 : LF (0, 1, 0) p ≤ ((177147 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_y) hp
  have bx2 : LF (0, 0, 1) p ≤ ((531441 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_z) hp
  have e0 : n0 ≤ 12 := by
    refine two_pow_le_lx ?_
    rw [← hn0]; simpa [LF] using bx0
  have e1 : n1 ≤ 11 := by
    refine two_pow_le_ly ?_
    rw [← hn1]; simpa [LF] using bx1
  have e2 : n2 ≤ 12 := by
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

/-- **`h(L₃(2)) ≥ 20`.**  A 20-vertex empty polytope in `{2ⁿ : n ∈ ℕ₀}³`. -/
theorem proof :
    ∃ V : Set (Fin 3 → ℝ),
      (V.Finite ∧
        V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (3 : ℝ) ^ n} ∧
        (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
        convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (3 : ℝ) ^ n} ⊆ V) ∧
      V.ncard = 20 :=
  ⟨VS, ⟨VS_finite, VS_subset, VS_convexPosition, VS_empty⟩, VS_ncard⟩

end Submissions.ExpLattice3Base3At20.Cert20
