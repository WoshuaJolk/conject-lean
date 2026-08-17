import Mathlib

/-!
# A 19-vertex empty polytope in the exponential lattice `L₃(2)`

This improves the 18-vertex certificate of Jig report 53 (statement
`ExpLattice3Base2At18`) and the prior published record of 10, which comes from the product
bound `h(S₁ × S₂) ≥ h(S₁)·h(S₂)` (Conforti–Di Summa, Theorem 2.6 of De Loera–La
Haye–Oliveros–Roldán-Pensado, Adv. Geom. 17 (2017) 473–482) together with `h(L₂(2)) = 5`
(ABFJN Corollary 4).  The vertex set was found by randomised greedy search over the
exponent box `{0, …, 5}³` and verified in exact integer arithmetic.

The proof is a finite integer certificate.  Convex position and emptiness are each
witnessed by an explicit integer linear functional.  The search over the infinite lattice
is complete: `conv V` lies in the coordinate bounding box `[1, 32] × [1, 32] × [1, 16]`, whose
powers of two are `2⁰, …, 2^5`, `2⁰, …, 2^5` and `2⁰, …, 2^4` respectively, so the
180 candidate lattice points enumerated below are the whole of it.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Submissions.ExpLattice3Base2At19.Cert19

/-- An exponent triple; the lattice point is `(2 ^ a, 2 ^ b, 2 ^ c)`. -/
abbrev T := ℕ × ℕ × ℕ

/-- The value at the lattice point of `t` of the integer functional `a`. -/
def dt (a : ℤ × ℤ × ℤ) (t : T) : ℤ :=
  a.1 * 2 ^ t.1 + a.2.1 * 2 ^ t.2.1 + a.2.2 * 2 ^ t.2.2

/-- The 19 exponent triples of the certificate. -/
def EX : List T :=
  [(0, 4, 4),
   (0, 5, 2),
   (1, 4, 4),
   (1, 5, 1),
   (1, 5, 2),
   (2, 5, 0),
   (2, 5, 1),
   (3, 3, 4),
   (3, 4, 3),
   (4, 0, 4),
   (4, 1, 4),
   (4, 3, 3),
   (4, 4, 2),
   (4, 4, 3),
   (5, 0, 3),
   (5, 1, 3),
   (5, 2, 2),
   (5, 3, 1),
   (5, 3, 2)]

/-- Convex-position certificates `(v, a, c)`: `⟪a, u⟫ ≤ c` for every other vertex `u`,
and `⟪a, v⟫ > c`. -/
def CP : List (T × (ℤ × ℤ × ℤ) × ℤ) :=
  [((0, 4, 4), ((-32), (-21), (-24)), (-784)),
   ((0, 5, 2), ((-16), 1, 0), 0),
   ((1, 4, 4), (14, 15, 28), 702),
   ((1, 5, 1), ((-32), (-21), (-28)), (-816)),
   ((1, 5, 2), (16, 21, 24), 784),
   ((2, 5, 0), ((-4), (-5), (-12)), (-192)),
   ((2, 5, 1), (12, 15, 8), 536),
   ((3, 3, 4), ((-8), (-8), (-7)), (-248)),
   ((3, 4, 3), ((-120), (-101), (-124)), (-3720)),
   ((4, 0, 4), ((-7), (-16), (-12)), (-336)),
   ((4, 1, 4), (60, 56, 127), 3048),
   ((4, 3, 3), ((-39), (-56), (-66)), (-1736)),
   ((4, 4, 2), ((-18), (-23), (-48)), (-856)),
   ((4, 4, 3), (26, 30, 45), 1252),
   ((5, 0, 3), ((-3), (-16), (-8)), (-192)),
   ((5, 1, 3), (8, 9, 14), 384),
   ((5, 2, 2), ((-7), (-16), (-14)), (-352)),
   ((5, 3, 1), ((-9), (-12), (-28)), (-448)),
   ((5, 3, 2), (6, 7, 6), 260)]

/-- Emptiness certificates `(q, a, c)`: `⟪a, v⟫ ≤ c` for every vertex `v` and `⟪a, q⟫ > c`,
one for each lattice point of the coordinate bounding box that is not a vertex. -/
def BAD : List (T × (ℤ × ℤ × ℤ) × ℤ) :=
  [((0, 0, 0), ((-64), (-45), (-56)), (-1680)),
   ((0, 0, 1), ((-64), (-45), (-56)), (-1680)),
   ((0, 0, 2), ((-64), (-45), (-56)), (-1680)),
   ((0, 0, 3), ((-64), (-45), (-56)), (-1680)),
   ((0, 0, 4), ((-64), (-45), (-56)), (-1680)),
   ((0, 1, 0), ((-64), (-45), (-56)), (-1680)),
   ((0, 1, 1), ((-64), (-45), (-56)), (-1680)),
   ((0, 1, 2), ((-64), (-45), (-56)), (-1680)),
   ((0, 1, 3), ((-64), (-45), (-56)), (-1680)),
   ((0, 1, 4), ((-64), (-45), (-56)), (-1680)),
   ((0, 2, 0), ((-64), (-45), (-56)), (-1680)),
   ((0, 2, 1), ((-64), (-45), (-56)), (-1680)),
   ((0, 2, 2), ((-64), (-45), (-56)), (-1680)),
   ((0, 2, 3), ((-64), (-45), (-56)), (-1680)),
   ((0, 2, 4), ((-64), (-45), (-56)), (-1680)),
   ((0, 3, 0), ((-64), (-45), (-56)), (-1680)),
   ((0, 3, 1), ((-64), (-45), (-56)), (-1680)),
   ((0, 3, 2), ((-64), (-45), (-56)), (-1680)),
   ((0, 3, 3), ((-64), (-45), (-56)), (-1680)),
   ((0, 3, 4), ((-64), (-45), (-56)), (-1680)),
   ((0, 4, 0), ((-64), (-45), (-56)), (-1680)),
   ((0, 4, 1), ((-64), (-45), (-56)), (-1680)),
   ((0, 4, 2), ((-64), (-45), (-56)), (-1680)),
   ((0, 4, 3), ((-64), (-45), (-56)), (-1680)),
   ((0, 5, 0), ((-64), (-45), (-56)), (-1680)),
   ((0, 5, 1), ((-64), (-45), (-56)), (-1680)),
   ((0, 5, 3), (0, 3, 4), 112),
   ((0, 5, 4), (0, 3, 4), 112),
   ((1, 0, 0), ((-64), (-45), (-56)), (-1680)),
   ((1, 0, 1), ((-64), (-45), (-56)), (-1680)),
   ((1, 0, 2), ((-64), (-45), (-56)), (-1680)),
   ((1, 0, 3), ((-64), (-45), (-56)), (-1680)),
   ((1, 0, 4), ((-64), (-45), (-56)), (-1680)),
   ((1, 1, 0), ((-64), (-45), (-56)), (-1680)),
   ((1, 1, 1), ((-64), (-45), (-56)), (-1680)),
   ((1, 1, 2), ((-64), (-45), (-56)), (-1680)),
   ((1, 1, 3), ((-64), (-45), (-56)), (-1680)),
   ((1, 1, 4), ((-64), (-45), (-56)), (-1680)),
   ((1, 2, 0), ((-64), (-45), (-56)), (-1680)),
   ((1, 2, 1), ((-64), (-45), (-56)), (-1680)),
   ((1, 2, 2), ((-64), (-45), (-56)), (-1680)),
   ((1, 2, 3), ((-64), (-45), (-56)), (-1680)),
   ((1, 2, 4), ((-64), (-45), (-56)), (-1680)),
   ((1, 3, 0), ((-64), (-45), (-56)), (-1680)),
   ((1, 3, 1), ((-64), (-45), (-56)), (-1680)),
   ((1, 3, 2), ((-64), (-45), (-56)), (-1680)),
   ((1, 3, 3), ((-64), (-45), (-56)), (-1680)),
   ((1, 3, 4), ((-64), (-45), (-56)), (-1680)),
   ((1, 4, 0), ((-64), (-45), (-56)), (-1680)),
   ((1, 4, 1), ((-64), (-45), (-56)), (-1680)),
   ((1, 4, 2), ((-64), (-45), (-56)), (-1680)),
   ((1, 4, 3), ((-64), (-45), (-56)), (-1680)),
   ((1, 5, 0), ((-64), (-45), (-56)), (-1680)),
   ((1, 5, 3), (0, 3, 4), 112),
   ((1, 5, 4), (0, 3, 4), 112),
   ((2, 0, 0), ((-64), (-45), (-56)), (-1680)),
   ((2, 0, 1), ((-64), (-45), (-56)), (-1680)),
   ((2, 0, 2), ((-64), (-45), (-56)), (-1680)),
   ((2, 0, 3), ((-64), (-45), (-56)), (-1680)),
   ((2, 0, 4), ((-64), (-45), (-56)), (-1680)),
   ((2, 1, 0), ((-64), (-45), (-56)), (-1680)),
   ((2, 1, 1), ((-64), (-45), (-56)), (-1680)),
   ((2, 1, 2), ((-64), (-45), (-56)), (-1680)),
   ((2, 1, 3), ((-64), (-45), (-56)), (-1680)),
   ((2, 1, 4), ((-64), (-45), (-56)), (-1680)),
   ((2, 2, 0), ((-64), (-45), (-56)), (-1680)),
   ((2, 2, 1), ((-64), (-45), (-56)), (-1680)),
   ((2, 2, 2), ((-64), (-45), (-56)), (-1680)),
   ((2, 2, 3), ((-64), (-45), (-56)), (-1680)),
   ((2, 2, 4), ((-64), (-45), (-56)), (-1680)),
   ((2, 3, 0), ((-64), (-45), (-56)), (-1680)),
   ((2, 3, 1), ((-64), (-45), (-56)), (-1680)),
   ((2, 3, 2), ((-64), (-45), (-56)), (-1680)),
   ((2, 3, 3), ((-64), (-45), (-56)), (-1680)),
   ((2, 3, 4), ((-64), (-45), (-56)), (-1680)),
   ((2, 4, 0), ((-64), (-45), (-56)), (-1680)),
   ((2, 4, 1), ((-64), (-45), (-56)), (-1680)),
   ((2, 4, 2), ((-64), (-45), (-56)), (-1680)),
   ((2, 4, 3), ((-64), (-45), (-56)), (-1680)),
   ((2, 4, 4), (7, 8, 12), 336),
   ((2, 5, 2), (4, 5, 4), 184),
   ((2, 5, 3), (0, 3, 4), 112),
   ((2, 5, 4), (0, 3, 4), 112),
   ((3, 0, 0), ((-64), (-45), (-56)), (-1680)),
   ((3, 0, 1), ((-64), (-45), (-56)), (-1680)),
   ((3, 0, 2), ((-64), (-45), (-56)), (-1680)),
   ((3, 0, 3), ((-64), (-45), (-56)), (-1680)),
   ((3, 0, 4), ((-64), (-45), (-56)), (-1680)),
   ((3, 1, 0), ((-64), (-45), (-56)), (-1680)),
   ((3, 1, 1), ((-64), (-45), (-56)), (-1680)),
   ((3, 1, 2), ((-64), (-45), (-56)), (-1680)),
   ((3, 1, 3), ((-64), (-45), (-56)), (-1680)),
   ((3, 1, 4), ((-64), (-45), (-56)), (-1680)),
   ((3, 2, 0), ((-64), (-45), (-56)), (-1680)),
   ((3, 2, 1), ((-64), (-45), (-56)), (-1680)),
   ((3, 2, 2), ((-64), (-45), (-56)), (-1680)),
   ((3, 2, 3), ((-64), (-45), (-56)), (-1680)),
   ((3, 2, 4), ((-64), (-45), (-56)), (-1680)),
   ((3, 3, 0), ((-64), (-45), (-56)), (-1680)),
   ((3, 3, 1), ((-64), (-45), (-56)), (-1680)),
   ((3, 3, 2), ((-64), (-45), (-56)), (-1680)),
   ((3, 3, 3), ((-64), (-45), (-56)), (-1680)),
   ((3, 4, 0), ((-64), (-45), (-56)), (-1680)),
   ((3, 4, 1), ((-64), (-45), (-56)), (-1680)),
   ((3, 4, 2), ((-64), (-45), (-56)), (-1680)),
   ((3, 4, 4), (7, 8, 12), 336),
   ((3, 5, 0), (6, 7, 0), 248),
   ((3, 5, 1), (6, 7, 0), 248),
   ((3, 5, 2), (6, 7, 0), 248),
   ((3, 5, 3), (0, 3, 4), 112),
   ((3, 5, 4), (0, 3, 4), 112),
   ((4, 0, 0), ((-64), (-45), (-56)), (-1680)),
   ((4, 0, 1), ((-64), (-45), (-56)), (-1680)),
   ((4, 0, 2), ((-64), (-45), (-56)), (-1680)),
   ((4, 0, 3), ((-64), (-45), (-56)), (-1680)),
   ((4, 1, 0), ((-64), (-45), (-56)), (-1680)),
   ((4, 1, 1), ((-64), (-45), (-56)), (-1680)),
   ((4, 1, 2), ((-64), (-45), (-56)), (-1680)),
   ((4, 1, 3), ((-64), (-45), (-56)), (-1680)),
   ((4, 2, 0), ((-64), (-45), (-56)), (-1680)),
   ((4, 2, 1), ((-64), (-45), (-56)), (-1680)),
   ((4, 2, 2), ((-64), (-45), (-56)), (-1680)),
   ((4, 2, 3), ((-64), (-45), (-56)), (-1680)),
   ((4, 2, 4), (1, 1, 2), 50),
   ((4, 3, 0), ((-64), (-45), (-56)), (-1680)),
   ((4, 3, 1), ((-64), (-45), (-56)), (-1680)),
   ((4, 3, 2), ((-64), (-45), (-56)), (-1680)),
   ((4, 3, 4), (7, 8, 12), 336),
   ((4, 4, 0), ((-7), (-9), (-20)), (-336)),
   ((4, 4, 1), ((-7), (-9), (-20)), (-336)),
   ((4, 4, 4), (4, 5, 4), 184),
   ((4, 5, 0), (6, 7, 0), 248),
   ((4, 5, 1), (6, 7, 0), 248),
   ((4, 5, 2), (6, 7, 0), 248),
   ((4, 5, 3), (0, 3, 4), 112),
   ((4, 5, 4), (0, 3, 4), 112),
   ((5, 0, 0), ((-15), (-32), (-28)), (-720)),
   ((5, 0, 1), ((-15), (-32), (-28)), (-720)),
   ((5, 0, 2), ((-15), (-32), (-28)), (-720)),
   ((5, 0, 4), (1, 0, 2), 48),
   ((5, 1, 0), ((-15), (-32), (-28)), (-720)),
   ((5, 1, 1), ((-15), (-32), (-28)), (-720)),
   ((5, 1, 2), ((-15), (-32), (-28)), (-720)),
   ((5, 1, 4), (1, 0, 2), 48),
   ((5, 2, 0), ((-15), (-32), (-28)), (-720)),
   ((5, 2, 1), ((-15), (-32), (-28)), (-720)),
   ((5, 2, 3), (7, 8, 12), 336),
   ((5, 2, 4), (1, 0, 2), 48),
   ((5, 3, 0), ((-7), (-9), (-20)), (-336)),
   ((5, 3, 3), (4, 5, 4), 184),
   ((5, 3, 4), (1, 0, 2), 48),
   ((5, 4, 0), (6, 7, 0), 248),
   ((5, 4, 1), (6, 7, 0), 248),
   ((5, 4, 2), (6, 7, 0), 248),
   ((5, 4, 3), (6, 7, 0), 248),
   ((5, 4, 4), (1, 0, 2), 48),
   ((5, 5, 0), (6, 7, 0), 248),
   ((5, 5, 1), (6, 7, 0), 248),
   ((5, 5, 2), (6, 7, 0), 248),
   ((5, 5, 3), (0, 3, 4), 112),
   ((5, 5, 4), (0, 3, 4), 112)]

/-- Every exponent triple in the box `{0, …, 5} × {0, …, 5} × {0, …, 4}`. -/
def BOX : List T :=
  (List.range 6).flatMap fun a => (List.range 6).flatMap fun b =>
    (List.range 5).map fun c => (a, b, c)

theorem cp_covers : ∀ t ∈ EX, t ∈ CP.map Prod.fst := by decide

theorem cp_ok : ∀ r ∈ CP,
    (∀ u ∈ EX, u ≠ r.1 → dt r.2.1 u ≤ r.2.2) ∧ r.2.2 < dt r.2.1 r.1 := by decide

theorem bad_covers : ∀ t ∈ BOX, t ∈ EX ∨ t ∈ BAD.map Prod.fst := by decide

theorem bad_ok : ∀ r ∈ BAD,
    (∀ u ∈ EX, dt r.2.1 u ≤ r.2.2) ∧ r.2.2 < dt r.2.1 r.1 := by decide

theorem box_x : ∀ u ∈ EX, dt (1, 0, 0) u ≤ 32 := by decide
theorem box_y : ∀ u ∈ EX, dt (0, 1, 0) u ≤ 32 := by decide
theorem box_z : ∀ u ∈ EX, dt (0, 0, 1) u ≤ 16 := by decide

theorem card_ok : EX.toFinset.card = 19 := by decide

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

theorem two_pow_le_4 {a : ℕ} (h : (2 : ℝ) ^ a ≤ 16) : a ≤ 4 := by
  by_contra hc
  have hk : 5 ≤ a := by omega
  have hpow : (2 : ℝ) ^ 5 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  linarith

theorem two_pow_le_5 {a : ℕ} (h : (2 : ℝ) ^ a ≤ 32) : a ≤ 5 := by
  by_contra hc
  have hk : 6 ≤ a := by omega
  have hpow : (2 : ℝ) ^ 6 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hk
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

theorem VS_ncard : VS.ncard = 19 := by
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
  have bx0 : LF (1, 0, 0) p ≤ ((32 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_x) hp
  have bx1 : LF (0, 1, 0) p ≤ ((32 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_y) hp
  have bx2 : LF (0, 0, 1) p ≤ ((16 : ℤ) : ℝ) := hull_le (LF_le_of_mem box_z) hp
  have e0 : n0 ≤ 5 := by
    refine two_pow_le_5 ?_
    rw [← hn0]; simpa [LF] using bx0
  have e1 : n1 ≤ 5 := by
    refine two_pow_le_5 ?_
    rw [← hn1]; simpa [LF] using bx1
  have e2 : n2 ≤ 4 := by
    refine two_pow_le_4 ?_
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

/-- **`h(L₃(2)) ≥ 19`.**  A 19-vertex empty polytope in `{2ⁿ : n ∈ ℕ₀}³`. -/
theorem proof :
    ∃ V : Set (Fin 3 → ℝ),
      (V.Finite ∧
        V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ∧
        (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
        convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ⊆ V) ∧
      V.ncard = 19 :=
  ⟨VS, ⟨VS_finite, VS_subset, VS_convexPosition, VS_empty⟩, VS_ncard⟩

end Submissions.ExpLattice3Base2At19.Cert19
