import Mathlib

/-!
# An 18-vertex empty polytope in the exponential lattice `L₃(2)`

This module proves `h(L₃(2)) ≥ 18`: the exponential lattice `{2ⁿ : n ∈ ℕ₀}³ ⊆ ℝ³`
contains a convex polytope with 18 vertices whose only lattice points are its vertices.
By Hoffman's proposition (ABFJN Proposition 1) this is `H({2ⁿ : n ∈ ℕ₀}³) ≥ 18`.

Prior published record: 10, from the product bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di
Summa, Theorem 2.6 of De Loera–La Haye–Oliveros–Roldán-Pensado, Adv. Geom. 17 (2017)
473–482) together with `h(L₂(2)) = 5` (Ambrus–Balko–Frankl–Jung–Naszódi, European J.
Combin. 116 (2024) 103884, Corollary 4).  The only explicitly written three-dimensional
construction in the literature has 3 vertices (Arun–Dillon, arXiv:2409.07262, Theorem 1.2
at α = 2).

The proof is a finite integer certificate.  Convex position and emptiness are each
witnessed by an explicit integer linear functional.  The search over the infinite lattice
is complete: `conv V` lies in the box `[1, 16]³`, and the only powers of two there are
`2⁰, …, 2⁴`, so 125 candidate lattice points is the whole of it.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Submissions.ExpLattice3Base2At18.Cert18

/-- An exponent triple; the lattice point is `(2 ^ a, 2 ^ b, 2 ^ c)`. -/
abbrev T := ℕ × ℕ × ℕ

/-- The value at the lattice point of `t` of the integer functional `a`. -/
def dt (a : ℤ × ℤ × ℤ) (t : T) : ℤ :=
  a.1 * 2 ^ t.1 + a.2.1 * 2 ^ t.2.1 + a.2.2 * 2 ^ t.2.2

/-- The 18 exponent triples of the certificate. -/
def EX : List T :=
  [(0, 1, 4),
   (0, 2, 4),
   (1, 0, 4),
   (1, 1, 4),
   (1, 4, 2),
   (2, 3, 3),
   (2, 4, 1),
   (2, 4, 2),
   (3, 2, 3),
   (3, 3, 2),
   (3, 3, 3),
   (3, 4, 0),
   (3, 4, 1),
   (4, 1, 2),
   (4, 2, 1),
   (4, 2, 2),
   (4, 3, 0),
   (4, 3, 1)]

/-- Convex-position certificates `(v, a, c)`: `⟪a, u⟫ ≤ c` for every other vertex `u`,
and `⟪a, v⟫ > c`. -/
def CP : List (T × (ℤ × ℤ × ℤ) × ℤ) :=
  [((0, 1, 4), ((-6), (-4), (-5)), (-96)),
   ((0, 2, 4), (0, 6, 7), 124),
   ((1, 0, 4), ((-4), (-6), (-5)), (-96)),
   ((1, 1, 4), (12, 4, 15), 268),
   ((1, 4, 2), ((-14), (-9), (-12)), (-224)),
   ((2, 3, 3), ((-24), (-18), (-23)), (-428)),
   ((2, 4, 1), ((-7), (-6), (-16)), (-168)),
   ((2, 4, 2), (12, 35, 36), 728),
   ((3, 2, 3), ((-18), (-24), (-23)), (-428)),
   ((3, 3, 2), ((-3), (-3), (-4)), (-68)),
   ((3, 3, 3), (14, 14, 19), 374),
   ((3, 4, 0), (0, 1, (-8)), 0),
   ((3, 4, 1), (6, 7, 8), 168),
   ((4, 1, 2), ((-9), (-14), (-12)), (-224)),
   ((4, 2, 1), ((-6), (-7), (-16)), (-168)),
   ((4, 2, 2), (14, 7, 17), 314),
   ((4, 3, 0), (1, 0, (-8)), 0),
   ((4, 3, 1), (7, 6, 8), 168)]

/-- Emptiness certificates `(q, a, c)`: `⟪a, v⟫ ≤ c` for every vertex `v` and `⟪a, q⟫ > c`,
one for each lattice point of the box `[1, 16]³` that is not a vertex. -/
def BAD : List (T × (ℤ × ℤ × ℤ) × ℤ) :=
  [((0, 0, 0), ((-10), (-7), (-9)), (-168)),
   ((0, 0, 1), ((-10), (-7), (-9)), (-168)),
   ((0, 0, 2), ((-10), (-7), (-9)), (-168)),
   ((0, 0, 3), ((-10), (-7), (-9)), (-168)),
   ((0, 0, 4), ((-10), (-7), (-9)), (-168)),
   ((0, 1, 0), ((-10), (-7), (-9)), (-168)),
   ((0, 1, 1), ((-10), (-7), (-9)), (-168)),
   ((0, 1, 2), ((-10), (-7), (-9)), (-168)),
   ((0, 1, 3), ((-10), (-7), (-9)), (-168)),
   ((0, 2, 0), ((-10), (-7), (-9)), (-168)),
   ((0, 2, 1), ((-10), (-7), (-9)), (-168)),
   ((0, 2, 2), ((-10), (-7), (-9)), (-168)),
   ((0, 2, 3), ((-10), (-7), (-9)), (-168)),
   ((0, 3, 0), ((-10), (-7), (-9)), (-168)),
   ((0, 3, 1), ((-10), (-7), (-9)), (-168)),
   ((0, 3, 2), ((-10), (-7), (-9)), (-168)),
   ((0, 3, 3), ((-10), (-7), (-9)), (-168)),
   ((0, 3, 4), (0, 1, 1), 20),
   ((0, 4, 0), ((-10), (-7), (-9)), (-168)),
   ((0, 4, 1), ((-10), (-7), (-9)), (-168)),
   ((0, 4, 2), ((-10), (-7), (-9)), (-168)),
   ((0, 4, 3), ((-12), 0, (-1)), (-28)),
   ((0, 4, 4), (0, 1, 1), 20),
   ((1, 0, 0), ((-10), (-7), (-9)), (-168)),
   ((1, 0, 1), ((-10), (-7), (-9)), (-168)),
   ((1, 0, 2), ((-10), (-7), (-9)), (-168)),
   ((1, 0, 3), ((-10), (-7), (-9)), (-168)),
   ((1, 1, 0), ((-10), (-7), (-9)), (-168)),
   ((1, 1, 1), ((-10), (-7), (-9)), (-168)),
   ((1, 1, 2), ((-10), (-7), (-9)), (-168)),
   ((1, 1, 3), ((-10), (-7), (-9)), (-168)),
   ((1, 2, 0), ((-10), (-7), (-9)), (-168)),
   ((1, 2, 1), ((-10), (-7), (-9)), (-168)),
   ((1, 2, 2), ((-10), (-7), (-9)), (-168)),
   ((1, 2, 3), ((-10), (-7), (-9)), (-168)),
   ((1, 2, 4), (4, 2, 5), 92),
   ((1, 3, 0), ((-10), (-7), (-9)), (-168)),
   ((1, 3, 1), ((-10), (-7), (-9)), (-168)),
   ((1, 3, 2), ((-10), (-7), (-9)), (-168)),
   ((1, 3, 3), ((-10), (-7), (-9)), (-168)),
   ((1, 3, 4), (0, 1, 1), 20),
   ((1, 4, 0), ((-10), (-7), (-9)), (-168)),
   ((1, 4, 1), ((-10), (-7), (-9)), (-168)),
   ((1, 4, 3), (0, 1, 1), 20),
   ((1, 4, 4), (0, 1, 1), 20),
   ((2, 0, 0), ((-10), (-7), (-9)), (-168)),
   ((2, 0, 1), ((-10), (-7), (-9)), (-168)),
   ((2, 0, 2), ((-10), (-7), (-9)), (-168)),
   ((2, 0, 3), ((-10), (-7), (-9)), (-168)),
   ((2, 0, 4), (6, 0, 7), 124),
   ((2, 1, 0), ((-10), (-7), (-9)), (-168)),
   ((2, 1, 1), ((-10), (-7), (-9)), (-168)),
   ((2, 1, 2), ((-10), (-7), (-9)), (-168)),
   ((2, 1, 3), ((-10), (-7), (-9)), (-168)),
   ((2, 1, 4), (6, 0, 7), 124),
   ((2, 2, 0), ((-10), (-7), (-9)), (-168)),
   ((2, 2, 1), ((-10), (-7), (-9)), (-168)),
   ((2, 2, 2), ((-10), (-7), (-9)), (-168)),
   ((2, 2, 3), ((-10), (-7), (-9)), (-168)),
   ((2, 2, 4), (6, 0, 7), 124),
   ((2, 3, 0), ((-10), (-7), (-9)), (-168)),
   ((2, 3, 1), ((-10), (-7), (-9)), (-168)),
   ((2, 3, 2), ((-10), (-7), (-9)), (-168)),
   ((2, 3, 4), (0, 1, 1), 20),
   ((2, 4, 0), ((-10), (-7), (-9)), (-168)),
   ((2, 4, 3), (0, 1, 1), 20),
   ((2, 4, 4), (0, 1, 1), 20),
   ((3, 0, 0), ((-10), (-7), (-9)), (-168)),
   ((3, 0, 1), ((-10), (-7), (-9)), (-168)),
   ((3, 0, 2), ((-10), (-7), (-9)), (-168)),
   ((3, 0, 3), ((-10), (-7), (-9)), (-168)),
   ((3, 0, 4), (6, 0, 7), 124),
   ((3, 1, 0), ((-10), (-7), (-9)), (-168)),
   ((3, 1, 1), ((-10), (-7), (-9)), (-168)),
   ((3, 1, 2), ((-10), (-7), (-9)), (-168)),
   ((3, 1, 3), ((-10), (-7), (-9)), (-168)),
   ((3, 1, 4), (6, 0, 7), 124),
   ((3, 2, 0), ((-10), (-7), (-9)), (-168)),
   ((3, 2, 1), ((-10), (-7), (-9)), (-168)),
   ((3, 2, 2), ((-10), (-7), (-9)), (-168)),
   ((3, 2, 4), (6, 0, 7), 124),
   ((3, 3, 0), ((-10), (-7), (-9)), (-168)),
   ((3, 3, 1), ((-10), (-7), (-9)), (-168)),
   ((3, 3, 4), (0, 1, 1), 20),
   ((3, 4, 2), (12, 11, 16), 312),
   ((3, 4, 3), (0, 1, 1), 20),
   ((3, 4, 4), (0, 1, 1), 20),
   ((4, 0, 0), ((-4), (-3), (-4)), (-72)),
   ((4, 0, 1), ((-7), (-10), (-9)), (-168)),
   ((4, 0, 2), ((-7), (-10), (-9)), (-168)),
   ((4, 0, 3), (6, 0, 7), 124),
   ((4, 0, 4), (6, 0, 7), 124),
   ((4, 1, 0), ((-7), (-10), (-9)), (-168)),
   ((4, 1, 1), ((-7), (-10), (-9)), (-168)),
   ((4, 1, 3), (6, 0, 7), 124),
   ((4, 1, 4), (6, 0, 7), 124),
   ((4, 2, 0), ((-7), (-10), (-9)), (-168)),
   ((4, 2, 3), (6, 0, 7), 124),
   ((4, 2, 4), (6, 0, 7), 124),
   ((4, 3, 2), (4, 2, 5), 92),
   ((4, 3, 3), (6, 0, 7), 124),
   ((4, 3, 4), (0, 1, 1), 20),
   ((4, 4, 0), (1, 1, 0), 24),
   ((4, 4, 1), (1, 1, 0), 24),
   ((4, 4, 2), (1, 1, 0), 24),
   ((4, 4, 3), (0, 1, 1), 20),
   ((4, 4, 4), (0, 1, 1), 20)]

/-- Every exponent triple in the box `{0, …, 4}³`. -/
def BOX : List T :=
  (List.range 5).flatMap fun a => (List.range 5).flatMap fun b =>
    (List.range 5).map fun c => (a, b, c)

theorem cp_covers : ∀ t ∈ EX, t ∈ CP.map Prod.fst := by decide

theorem cp_ok : ∀ r ∈ CP,
    (∀ u ∈ EX, u ≠ r.1 → dt r.2.1 u ≤ r.2.2) ∧ r.2.2 < dt r.2.1 r.1 := by decide

theorem bad_covers : ∀ t ∈ BOX, t ∈ EX ∨ t ∈ BAD.map Prod.fst := by decide

theorem bad_ok : ∀ r ∈ BAD,
    (∀ u ∈ EX, dt r.2.1 u ≤ r.2.2) ∧ r.2.2 < dt r.2.1 r.1 := by decide

theorem box_x : ∀ u ∈ EX, dt (1, 0, 0) u ≤ 16 := by decide
theorem box_y : ∀ u ∈ EX, dt (0, 1, 0) u ≤ 16 := by decide
theorem box_z : ∀ u ∈ EX, dt (0, 0, 1) u ≤ 16 := by decide

theorem card_ok : EX.toFinset.card = 18 := by decide

/-- The lattice point of `L₃(2)` with exponent triple `t`. -/
def rp (t : T) : Fin 3 → ℝ := ![2 ^ t.1, 2 ^ t.2.1, 2 ^ t.2.2]

/-- The real linear functional with integer coefficient triple `a`. -/
def LF (a : ℤ × ℤ × ℤ) (x : Fin 3 → ℝ) : ℝ :=
  (a.1 : ℝ) * x 0 + (a.2.1 : ℝ) * x 1 + (a.2.2 : ℝ) * x 2

/-- The vertex set. -/
def VS : Set (Fin 3 → ℝ) := rp '' (↑EX.toFinset : Set T)

/-- The exponential lattice `L₃(2)`. -/
def S3 : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n}

-- ## Bridging the integer certificates to the real convex hull

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

-- ## Powers of two

theorem two_pow_inj {a b : ℕ} (h : (2 : ℝ) ^ a = 2 ^ b) : a = b := by
  have h' : ((2 ^ a : ℕ) : ℝ) = ((2 ^ b : ℕ) : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h')

theorem two_pow_le_four {a : ℕ} (h : (2 : ℝ) ^ a ≤ 16) : a ≤ 4 := by
  by_contra hc
  have h5 : 5 ≤ a := by omega
  have hpow : (2 : ℝ) ^ 5 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) h5
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

-- ## Membership helpers

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

-- ## The four conditions of "empty polytope"

theorem VS_finite : VS.Finite := (EX.toFinset.finite_toSet).image rp

theorem VS_ncard : VS.ncard = 18 := by
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
  have bx0 : LF (1, 0, 0) p ≤ ((16 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_x) hp
  have bx1 : LF (0, 1, 0) p ≤ ((16 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_y) hp
  have bx2 : LF (0, 0, 1) p ≤ ((16 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_z) hp
  have e0 : n0 ≤ 4 := by
    refine two_pow_le_four ?_
    rw [← hn0]; simpa [LF] using bx0
  have e1 : n1 ≤ 4 := by
    refine two_pow_le_four ?_
    rw [← hn1]; simpa [LF] using bx1
  have e2 : n2 ≤ 4 := by
    refine two_pow_le_four ?_
    rw [← hn2]; simpa [LF] using bx2
  have hbox : (n0, n1, n2) ∈ BOX := by
    simp only [BOX, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨n0, by omega, n1, by omega, n2, by omega, rfl⟩
  rcases bad_covers _ hbox with hin | hbad
  · rw [hpe]; exact mem_VS hin
  · exfalso
    obtain ⟨r, hrBAD, hr1⟩ := List.mem_map.mp hbad
    obtain ⟨hle, hgt⟩ := bad_ok r hrBAD
    refine not_mem_hull (LF_le_of_mem hle) ?_ hp
    rw [hpe, ← hr1, LF_rp]
    exact_mod_cast hgt

/-- **`h(L₃(2)) ≥ 18`.**  An 18-vertex empty polytope in `{2ⁿ : n ∈ ℕ₀}³`. -/
theorem proof :
    ∃ V : Set (Fin 3 → ℝ),
      (V.Finite ∧
        V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ∧
        (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
        convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ⊆ V) ∧
      V.ncard = 18 :=
  ⟨VS, ⟨VS_finite, VS_subset, VS_convexPosition, VS_empty⟩, VS_ncard⟩

end Submissions.ExpLattice3Base2At18.Cert18
