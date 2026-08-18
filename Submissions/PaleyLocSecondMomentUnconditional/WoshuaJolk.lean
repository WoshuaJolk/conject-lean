import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Commons.PaleyLocalizationTheta

/-!
# Problem 26's upper half, unconditionally reduced to one spectral quantity

Proof of `Statements.PaleyLocSecondMomentUnconditional.statement`.  Three parts.

**Part one, the general ceiling.**  For a `d`-regular graph on `m` vertices, let `X` be
feasible for the program defining `Commons.thetaClique adj`, write `⟪M, X⟫ = ∑ᵤ∑ᵥ Mᵤᵥ Xᵤᵥ`
and `s = ∑ᵤ∑ᵥ Xᵤᵥ`.  Since `X` vanishes off the edges and the diagonal, three pairings are
forced: `⟪1, X⟫ = 1`, `⟪A, X⟫ = s - 1`, `⟪A², X⟫ = d + ⟪R, X⟫ + (d²/m)(s-1)`.  With
`B = A - (d/m)J` one gets `(B²)ᵤᵥ = (A²)ᵤᵥ - d²/m` entrywise, hence `⟪B, X⟫ = s(m-d)/m - 1`
and `⟪B², X⟫ = d - d²/m + ⟪R, X⟫`.  Cauchy–Schwarz inside the semidefinite cone: with
`t = ⟪B, X⟫`, the matrix `(B - t·1)²` is the square of a symmetric matrix hence positive
semidefinite, so `⟪(B - t·1)², X⟫ ≥ 0`, and with `tr X = 1` this is `t² ≤ ⟪B², X⟫`.  Finally
`⟪R, X⟫ ≤ c` because `c·1 - R ⪰ 0`.

**Part two, the two counts.**  Let `χ` be the quadratic character mod `p`.  From
`∑ₐ χ(a) = 0` and the fact that `χ` is `1` on nonzero squares and `-1` on non-squares, the
nonzero squares number `(p-1)/2`, which is the vertex count.  For the degree, fix a nonzero
square `u`; then

    ∑_y (1 + χ(y))(1 + χ(u-y)) = p + 0 + 0 + ∑_y χ(y)χ(u-y),

and substituting `y = ut` turns the last sum into `χ(u)² · ∑_t χ(t)χ(1-t) = jacobiSum χ χ`,
which is `-χ(-1) = -1` because `χ⁻¹ = χ` and `p ≡ 1 (mod 4)` makes `-1` a square.  The left
side is `4·#{y : χ(y) = χ(u-y) = 1} + 4` — the two exceptional terms `y = 0` and `y = u` each
contribute `2` — so the degree is `(p-5)/4`.

**Part three.**  `paleyLocAdj p` is irreflexive since `u - u = 0` is not a *nonzero* square,
and symmetric since `-1` is a square, so `v - u = (-1)(u - v)`.  Feeding `m = (p-1)/2` and
`d = (p-5)/4` into part one and weakening `2(p-1)/(p+3) ≤ 2` and
`(p-5)(p+3)/(2(p-1)) ≤ p/2` gives the stated bound.
-/

open scoped MatrixOrder Matrix
open Finset

namespace Submissions.PaleyLocSecondMomentUnconditional.WoshuaJolk

section GeneralCeiling


variable {V : Type*} [Fintype V] [DecidableEq V]

lemma trace_mul_nonneg {M X : Matrix V V ℝ} (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hB' : M = Bᴴ * B := by rw [hB]; rfl
  have h1 : (M * X).trace = (B * X * Bᴴ).trace := by
    rw [hB', Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  rw [h1]
  exact (hX.mul_mul_conjTranspose_same (B := B)).trace_nonneg

/-- The pairing `⟪M, X⟫ = ∑ᵤ∑ᵥ Mᵤᵥ Xᵤᵥ`. -/
noncomputable def ip (M X : Matrix V V ℝ) : ℝ := ∑ u, ∑ v, M u v * X u v

lemma ip_eq_trace {M X : Matrix V V ℝ} (hX : ∀ u v, X v u = X u v) :
    ip M X = (M * X).trace := by
  simp only [ip, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hX v u]

lemma ip_add (M N X : Matrix V V ℝ) : ip (M + N) X = ip M X + ip N X := by
  simp [ip, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma ip_smul (a : ℝ) (M X : Matrix V V ℝ) : ip (a • M) X = a * ip M X := by
  simp [ip, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma ip_sub (M N X : Matrix V V ℝ) : ip (M - N) X = ip M X - ip N X := by
  simp [ip, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Setup bundle for the argument. -/
structure Setup (adj : V → V → Prop) (A R : Matrix V V ℝ) (m d c : ℝ) : Prop where
  hm : m = (Fintype.card V : ℝ)
  hsymm : ∀ u v, adj u v → adj v u
  hirr : ∀ u, ¬ adj u u
  hA1 : ∀ u v, adj u v → A u v = 1
  hA0 : ∀ u v, ¬ adj u v → A u v = 0
  hrow : ∀ u, ∑ v, A u v = d
  hRdiag : ∀ u, R u u = 0
  hR : ∀ u v, adj u v → R u v = (A * A) u v - d ^ 2 / m
  hc : (c • (1 : Matrix V V ℝ) - R).PosSemidef

variable {adj : V → V → Prop} {A R : Matrix V V ℝ} {m d c : ℝ}

lemma Setup.A_symm (S : Setup adj A R m d c) (u v : V) : A v u = A u v := by
  by_cases h : adj u v
  · rw [S.hA1 u v h, S.hA1 v u (S.hsymm u v h)]
  · rw [S.hA0 u v h, S.hA0 v u (fun hh => h (S.hsymm v u hh))]

lemma Setup.A_diag (S : Setup adj A R m d c) (u : V) : A u u = 0 :=
  S.hA0 u u (S.hirr u)

lemma Setup.A_sq_self (S : Setup adj A R m d c) (u v : V) : A u v * A u v = A u v := by
  by_cases h : adj u v
  · rw [S.hA1 u v h]; ring
  · rw [S.hA0 u v h]; ring

lemma Setup.AA_diag (S : Setup adj A R m d c) (u : V) : (A * A) u u = d := by
  rw [Matrix.mul_apply]
  rw [← S.hrow u]
  exact Finset.sum_congr rfl fun w _ => by rw [S.A_symm u w, S.A_sq_self u w]

lemma Setup.m_pos (S : Setup adj A R m d c) : 0 < m := by
  rw [S.hm]
  exact_mod_cast Fintype.card_pos

lemma Setup.d_lt_m (S : Setup adj A R m d c) : d < m := by
  obtain ⟨u⟩ := ‹Nonempty V›
  have h1 : d = ∑ v ∈ Finset.univ.erase u, A u v := by
    rw [← S.hrow u, ← Finset.sum_erase_add _ _ (Finset.mem_univ u), S.A_diag u, add_zero]
  have h2 : ∑ v ∈ Finset.univ.erase u, A u v ≤ ((Finset.univ.erase u).card : ℝ) := by
    calc ∑ v ∈ Finset.univ.erase u, A u v ≤ ∑ _v ∈ Finset.univ.erase u, (1:ℝ) := by
          refine Finset.sum_le_sum fun v _ => ?_
          by_cases h : adj u v
          · rw [S.hA1 u v h]
          · rw [S.hA0 u v h]; norm_num
      _ = ((Finset.univ.erase u).card : ℝ) := by simp
  have h3 : ((Finset.univ.erase u).card : ℝ) = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, S.hm]
    have : 1 ≤ Fintype.card V := Fintype.card_pos
    push_cast [Nat.cast_sub this]
    ring
  rw [h1]
  linarith [h2, h3.le, h3.ge]

end Main

section Main2

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {adj : V → V → Prop} {A R : Matrix V V ℝ} {m d c : ℝ}

/-- The all-ones matrix. -/
def allOnes (V : Type*) : Matrix V V ℝ := Matrix.of fun _ _ => (1 : ℝ)

@[simp] lemma allOnes_apply (u v : V) : allOnes V u v = 1 := rfl

variable {X : Matrix V V ℝ}

lemma X_symm (hX : X.PosSemidef) (u v : V) : X v u = X u v := by
  have := hX.isHermitian.apply u v
  simpa using this

lemma ip_one (hX : X.PosSemidef) : ip (1 : Matrix V V ℝ) X = X.trace := by
  rw [ip_eq_trace (X_symm hX), one_mul]

lemma ip_allOnes : ip (allOnes V) X = ∑ u, ∑ v, X u v := by
  simp [ip]

lemma Setup.ip_A (S : Setup adj A R m d c) (hX : X.PosSemidef)
    (hz : ∀ u v, u ≠ v → ¬ adj u v → X u v = 0) :
    ip A X = (∑ u, ∑ v, X u v) - X.trace := by
  have key : ∀ u v : V, A u v * X u v = X u v - (1 : Matrix V V ℝ) u v * X u v := by
    intro u v
    by_cases huv : u = v
    · subst huv; rw [S.A_diag u]; simp
    · by_cases h : adj u v
      · rw [S.hA1 u v h, Matrix.one_apply_ne huv]; ring
      · rw [S.hA0 u v h, hz u v huv h]; ring
  have : ip A X = (∑ u, ∑ v, X u v) - ip (1 : Matrix V V ℝ) X := by
    simp only [ip, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => key u v
  rw [this, ip_one hX]

lemma Setup.ip_AA (S : Setup adj A R m d c) (hX : X.PosSemidef)
    (hz : ∀ u v, u ≠ v → ¬ adj u v → X u v = 0) :
    ip (A * A) X = d * ip (1 : Matrix V V ℝ) X + ip R X + (d ^ 2 / m) * ip A X := by
  have key : ∀ u v : V, (A * A) u v * X u v
      = d * ((1 : Matrix V V ℝ) u v * X u v) + R u v * X u v + (d ^ 2 / m) * (A u v * X u v) := by
    intro u v
    by_cases huv : u = v
    · subst huv; rw [S.AA_diag u, S.hRdiag u, S.A_diag u, Matrix.one_apply_eq]; ring
    · by_cases h : adj u v
      · rw [S.hA1 u v h, Matrix.one_apply_ne huv, S.hR u v h]; ring
      · rw [hz u v huv h]; ring
  have inner : ∀ u : V, ∑ v, (A * A) u v * X u v
      = (∑ v, d * ((1 : Matrix V V ℝ) u v * X u v)) + (∑ v, R u v * X u v)
        + (∑ v, (d ^ 2 / m) * (A u v * X u v)) := by
    intro u
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => key u v
  show (∑ u, ∑ v, (A * A) u v * X u v) = _
  rw [Finset.sum_congr rfl fun u _ => inner u, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [ip, Finset.mul_sum]

lemma Setup.ip_R_le (S : Setup adj A R m d c) (hX : X.PosSemidef) (htr : X.trace = 1) :
    ip R X ≤ c := by
  have h0 : 0 ≤ ((c • (1 : Matrix V V ℝ) - R) * X).trace := trace_mul_nonneg S.hc hX
  rw [← ip_eq_trace (X_symm hX)] at h0
  have : ip (c • (1 : Matrix V V ℝ) - R) X = c * X.trace - ip R X := by
    rw [ip_sub, ip_smul, ip_one hX]
  rw [this, htr, mul_one] at h0
  linarith

lemma Setup.BB_apply (S : Setup adj A R m d c) (u v : V) :
    ∑ w : V, (A u w - d / m) * (A w v - d / m) = (A * A) u v - d ^ 2 / m := by
  have hm0 : m ≠ 0 := ne_of_gt S.m_pos
  have hcol : ∑ w : V, A w v = d := by
    rw [← S.hrow v]; exact Finset.sum_congr rfl fun w _ => S.A_symm v w
  have expand : ∑ w : V, (A u w - d / m) * (A w v - d / m)
      = (∑ w : V, A u w * A w v) - (d / m) * (∑ w : V, A u w)
        - (d / m) * (∑ w : V, A w v) + (Fintype.card V : ℝ) * (d / m) ^ 2 := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ]
    ring
  rw [expand, S.hrow u, hcol, ← S.hm, Matrix.mul_apply]
  have hmm : m * (d / m) ^ 2 = d ^ 2 / m := by field_simp
  rw [hmm]
  ring

end Main2

section Final

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {adj : V → V → Prop} {A R : Matrix V V ℝ} {m d c : ℝ} {X : Matrix V V ℝ}

/-- The centred adjacency matrix `B = A - (d/m) J`. -/
noncomputable def cadj (A : Matrix V V ℝ) (d m : ℝ) : Matrix V V ℝ :=
  A - (d / m) • allOnes V

@[simp] lemma cadj_apply (A : Matrix V V ℝ) (d m : ℝ) (u v : V) :
    cadj A d m u v = A u v - d / m := by
  simp [cadj, allOnes]

lemma cadj_symm (S : Setup adj A R m d c) (u v : V) : cadj A d m v u = cadj A d m u v := by
  simp [S.A_symm u v]

/-- The Cauchy–Schwarz step: `⟪B,X⟫² ≤ ⟪B²,X⟫` when `tr X = 1`. -/
lemma cs_step {B : Matrix V V ℝ} (hBsymm : ∀ u v, B v u = B u v)
    (hX : X.PosSemidef) (htr : X.trace = 1) :
    (ip B X) ^ 2 ≤ ip (B * B) X := by
  set t := ip B X with ht
  set C : Matrix V V ℝ := B - t • (1 : Matrix V V ℝ) with hC
  have hCT : Cᴴ = C := by
    ext u v
    simp only [hC, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
      star_sub, star_mul', RCLike.star_def, starRingEnd_apply, star_trivial, smul_eq_mul]
    rw [hBsymm u v, Matrix.one_apply, Matrix.one_apply]
    by_cases h : v = u
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hpsd : (C * C).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self C
    rwa [hCT] at this
  have h0 : 0 ≤ ip (C * C) X := by
    rw [ip_eq_trace (X_symm hX)]; exact trace_mul_nonneg hpsd hX
  have hCCm : C * C = B * B - (2 * t) • B + (t ^ 2) • (1 : Matrix V V ℝ) := by
    simp only [hC, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
    module
  have hCC : ∀ u v : V, (C * C) u v
      = (B * B) u v - (2 * t) * B u v + t ^ 2 * (1 : Matrix V V ℝ) u v := by
    intro u v
    rw [hCCm]
    simp
  have hkey : ip (C * C) X = ip (B * B) X - (2 * t) * ip B X + t ^ 2 * ip (1 : Matrix V V ℝ) X := by
    have inner : ∀ u : V, ∑ v, (C * C) u v * X u v
        = (∑ v, (B * B) u v * X u v) - (∑ v, (2 * t) * (B u v * X u v))
          + (∑ v, t ^ 2 * ((1 : Matrix V V ℝ) u v * X u v)) := by
      intro u
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by rw [hCC u v]; ring
    show (∑ u, ∑ v, (C * C) u v * X u v) = _
    rw [Finset.sum_congr rfl fun u _ => inner u, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [ip, Finset.mul_sum]
  rw [hkey, ip_one hX, htr, mul_one] at h0
  nlinarith [h0]

/-- **Main bound.** -/
theorem quad_bound (S : Setup adj A R m d c) (hX : X.PosSemidef) (htr : X.trace = 1)
    (hz : ∀ u v, u ≠ v → ¬ adj u v → X u v = 0) (s : ℝ) (hs : s = ∑ u, ∑ v, X u v) :
    (s * ((m - d) / m) - 1) ^ 2 ≤ d - d ^ 2 / m + c := by
  have hm0 : m ≠ 0 := ne_of_gt S.m_pos
  set B := cadj A d m with hB
  have hBsymm : ∀ u v, B v u = B u v := cadj_symm S
  -- ⟪B,X⟫
  have hipB : ip B X = s * ((m - d) / m) - 1 := by
    have : ip B X = ip A X - (d / m) * ip (allOnes V) X := by
      rw [hB, cadj, ip_sub, ip_smul]
    rw [this, S.ip_A hX hz, ip_allOnes, htr, ← hs]
    field_simp
    ring
  -- ⟪B*B,X⟫
  have hBB : ∀ u v : V, (B * B) u v = (A * A) u v - d ^ 2 / m * (allOnes V) u v := by
    intro u v
    have : (B * B) u v = ∑ w : V, (A u w - d / m) * (A w v - d / m) := by
      simp [hB, Matrix.mul_apply]
    rw [this, S.BB_apply u v]
    simp
  have hipBB : ip (B * B) X = ip (A * A) X - (d ^ 2 / m) * ip (allOnes V) X := by
    have inner : ∀ u : V, ∑ v, (B * B) u v * X u v
        = (∑ v, (A * A) u v * X u v) - (∑ v, (d ^ 2 / m) * ((allOnes V) u v * X u v)) := by
      intro u
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by rw [hBB u v]; ring
    show (∑ u, ∑ v, (B * B) u v * X u v) = _
    rw [Finset.sum_congr rfl fun u _ => inner u, Finset.sum_sub_distrib]
    simp only [ip, Finset.mul_sum]
  have hAA := S.ip_AA hX hz
  have hipA : ip A X = s - 1 := by rw [S.ip_A hX hz, htr, ← hs]
  have hipR : ip R X ≤ c := S.ip_R_le hX htr
  have hip1 : ip (1 : Matrix V V ℝ) X = 1 := by rw [ip_one hX, htr]
  have hipJ : ip (allOnes V) X = s := by rw [ip_allOnes, ← hs]
  have hfin : ip (B * B) X = d - d ^ 2 / m + ip R X := by
    rw [hipBB, hAA, hip1, hipA, hipJ]
    field_simp
    ring
  have hcs := cs_step hBsymm hX htr
  rw [hipB, hfin] at hcs
  linarith

end Final

section Cor

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {adj : V → V → Prop} {A R : Matrix V V ℝ} {m d c : ℝ}

theorem thetaClique_le (S : Setup adj A R m d c) :
    Commons.thetaClique adj ≤ (m / (m - d)) * (1 + Real.sqrt (d - d ^ 2 / m + c)) := by
  have hmd : 0 < m - d := by have := S.d_lt_m; linarith
  have hm0 : 0 < m := S.m_pos
  have hrhs : 0 ≤ (m / (m - d)) * (1 + Real.sqrt (d - d ^ 2 / m + c)) := by positivity
  refine Real.sSup_le ?_ hrhs
  rintro s ⟨X, hX, htr, hz, hs⟩
  have h := quad_bound S hX htr hz s hs
  have hK : (0:ℝ) ≤ d - d ^ 2 / m + c := le_trans (sq_nonneg _) h
  have habs : s * ((m - d) / m) - 1 ≤ Real.sqrt (d - d ^ 2 / m + c) := by
    have h1 : |s * ((m - d) / m) - 1| ≤ Real.sqrt (d - d ^ 2 / m + c) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h
    exact le_trans (le_abs_self _) h1
  have hpos : 0 < (m - d) / m := div_pos hmd hm0
  have hstep : s ≤ (1 + Real.sqrt (d - d ^ 2 / m + c)) / ((m - d) / m) := by
    rw [le_div_iff₀ hpos]; linarith
  refine le_trans hstep (le_of_eq ?_)
  field_simp

end Cor


end GeneralCeiling

section Counts


variable {p : ℕ} [Fact (Nat.Prime p)]

lemma card_sq (hp2 : p ≠ 2) :
    2 * Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} + 1 = p := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set χ := quadraticChar (ZMod p) with hχ
  set S := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ IsSquare x) with hS
  set N := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ ¬ IsSquare x) with hN
  have hpt : ∀ a : ZMod p,
      χ a = (if a ∈ S then (1:ℤ) else 0) - (if a ∈ N then (1:ℤ) else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [hS, hN, hχ]
    · by_cases hsq : IsSquare a
      · have h1 : χ a = 1 := (quadraticChar_one_iff_isSquare ha).mpr hsq
        simp [hS, hN, ha, hsq, h1]
      · have h1 : χ a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hsq
        simp [hS, hN, ha, hsq, h1]
  have h0 : ∑ a : ZMod p, χ a = 0 := quadraticChar_sum_zero hchar
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib] at h0
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
  have hcards : S.card = N.card := by exact_mod_cast sub_eq_zero.mp h0
  have hSe : S = (univ.erase (0 : ZMod p)).filter (fun x => IsSquare x) := by
    ext x; simp [hS, Finset.mem_erase]
  have hNe : N = (univ.erase (0 : ZMod p)).filter (fun x => ¬ IsSquare x) := by
    ext x; simp [hN, Finset.mem_erase]
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  have hp1 : 1 ≤ p := (Fact.out (p := Nat.Prime p)).one_lt.le.trans' (by norm_num)
  have hunion : S.card + N.card = p - 1 := by
    rw [hSe, hNe, Finset.card_filter_add_card_filter_not,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardp]
  have hsub : Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} = S.card := by
    rw [hS, Fintype.card_subtype]
  rw [hsub]
  omega


/-- `χ(-1) = 1` when `p ≡ 1 (mod 4)`. -/
lemma chi_neg_one (h4 : p % 4 = 1) : quadraticChar (ZMod p) (-1) = 1 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  have hp1 := (Fact.out (p := Nat.Prime p)).one_lt
  have hne : (-1 : ZMod p) ≠ 0 := by
    simpa using (fun h : (1 : ZMod p) = 0 => one_ne_zero h)
  refine (quadraticChar_one_iff_isSquare hne).mpr ?_
  exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)

/-- The quadratic character is its own inverse. -/
lemma chi_inv : (quadraticChar (ZMod p))⁻¹ = quadraticChar (ZMod p) := by
  refine MulChar.ext' ?_
  intro a
  rw [MulChar.inv_apply']
  by_cases ha : a = 0
  · subst ha; simp
  · have hmul : quadraticChar (ZMod p) a⁻¹ * quadraticChar (ZMod p) a = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ha, map_one]
    rcases quadraticChar_dichotomy ha with h | h <;> rw [h] at hmul ⊢ <;> omega

lemma chi_ne_one (hp2 : p ≠ 2) : quadraticChar (ZMod p) ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hchar
  intro h
  rw [h] at ha
  by_cases h0 : IsUnit a
  · rw [MulChar.one_apply h0] at ha; norm_num at ha
  · rw [MulChar.map_nonunit _ h0] at ha; norm_num at ha

/-- The key Jacobi sum: `∑ₜ χ(t)χ(1-t) = -1` when `p ≡ 1 (mod 4)`. -/
lemma jacobi_val (hp2 : p ≠ 2) (h4 : p % 4 = 1) :
    jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = -1 := by
  have h := jacobiSum_nontrivial_inv (χ := quadraticChar (ZMod p)) (chi_ne_one hp2)
  rw [chi_inv] at h
  rw [h, chi_neg_one h4]


/-- The degree count: for `u` a nonzero square mod `p ≡ 1 (mod 4)`, the number of `y` with
both `y` and `u - y` nonzero squares is `(p-5)/4`. -/
lemma degree_count (hp2 : p ≠ 2) (h4 : p % 4 = 1) (u : ZMod p)
    (hu : quadraticChar (ZMod p) u = 1) :
    4 * ((univ : Finset (ZMod p)).filter
        (fun y => quadraticChar (ZMod p) y = 1 ∧ quadraticChar (ZMod p) (u - y) = 1)).card + 5
      = p := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  set χ := quadraticChar (ZMod p) with hχ
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; rw [hχ, quadraticChar_zero] at hu; norm_num at hu
  have hsum1 : ∑ y : ZMod p, χ y = 0 := quadraticChar_sum_zero hchar
  have hsum2 : ∑ y : ZMod p, χ (u - y) = 0 := by
    rw [← hsum1]
    exact Fintype.sum_equiv (Equiv.subLeft u) _ _ (fun _ => rfl)
  have hJ : ∑ y : ZMod p, χ y * χ (u - y) = -1 := by
    have hre : ∑ t : ZMod p, χ (u * t) * χ (u - u * t) = ∑ y : ZMod p, χ y * χ (u - y) :=
      Fintype.sum_equiv (Equiv.mulLeft₀ u hu0) _ _ (fun _ => rfl)
    have hpt : ∀ t : ZMod p, χ (u * t) * χ (u - u * t) = χ t * χ (1 - t) := by
      intro t
      have h1 : u - u * t = u * (1 - t) := by ring
      rw [h1, map_mul, map_mul, hu]
      ring
    rw [← hre, Finset.sum_congr rfl (fun t _ => hpt t)]
    have := jacobi_val (p := p) hp2 h4
    rw [jacobiSum] at this
    rw [← this]
  have hchi0 : χ (0 : ZMod p) = 0 := by rw [hχ]; exact quadraticChar_zero
  have hpt : ∀ y : ZMod p, (1 + χ y) * (1 + χ (u - y))
      = 4 * (if (χ y = 1 ∧ χ (u - y) = 1) then (1:ℤ) else 0)
        + 2 * (if y = 0 then (1:ℤ) else 0) + 2 * (if y = u then (1:ℤ) else 0) := by
    intro y
    by_cases hy0 : y = 0
    · have hyu : ¬ (y = u) := by rw [hy0]; exact fun h => hu0 h.symm
      have h1 : χ y = 0 := by rw [hy0]; exact hchi0
      have h2 : u - y = u := by rw [hy0]; ring
      rw [h1, h2, hu, if_neg hyu, if_pos hy0]
      norm_num
    · by_cases hyu : y = u
      · have h1 : χ y = 1 := by rw [hyu]; exact hu
        have h2 : u - y = 0 := by rw [hyu]; ring
        rw [h1, h2, hchi0, if_neg hy0, if_pos hyu]
        norm_num
      · have hd0 : u - y ≠ 0 := fun h => hyu (sub_eq_zero.mp h).symm
        rw [if_neg hy0, if_neg hyu]
        rcases quadraticChar_dichotomy hy0 with h1 | h1 <;>
          rcases quadraticChar_dichotomy hd0 with h2 | h2 <;>
            rw [← hχ] at h1 h2 <;> rw [h1, h2] <;> norm_num
  have hleft : ∑ y : ZMod p, (1 + χ y) * (1 + χ (u - y)) = (p : ℤ) - 1 := by
    have hexp : ∀ y : ZMod p, (1 + χ y) * (1 + χ (u - y))
        = 1 + χ y + χ (u - y) + χ y * χ (u - y) := by intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => hexp y)]
    simp only [Finset.sum_add_distrib, hsum1, hsum2, hJ, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hpt y)] at hleft
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at hleft
  have hc0 : ((univ : Finset (ZMod p)).filter (fun x : ZMod p => x = 0)).card = 1 := by rw [Finset.filter_eq']; simp
  have hcu : ((univ : Finset (ZMod p)).filter (fun x : ZMod p => x = u)).card = 1 := by rw [Finset.filter_eq']; simp
  rw [hc0, hcu] at hleft
  have h5 : (4 : ℤ) * (((univ : Finset (ZMod p)).filter
      (fun y => χ y = 1 ∧ χ (u - y) = 1)).card : ℤ) + 5 = (p : ℤ) := by push_cast at hleft ⊢; linarith
  exact_mod_cast h5


/-- `IsNonzeroSq` is exactly `χ = 1`. -/
lemma isNonzeroSq_iff (z : ZMod p) :
    Commons.IsNonzeroSq z ↔ quadraticChar (ZMod p) z = 1 := by
  constructor
  · rintro ⟨hz, hsq⟩
    exact (quadraticChar_one_iff_isSquare hz).mpr hsq
  · intro h
    have hz : z ≠ 0 := by
      intro hh; rw [hh, quadraticChar_zero] at h; norm_num at h
    exact ⟨hz, (quadraticChar_one_iff_isSquare hz).mp h⟩

variable [NeZero p]

lemma card_paleyLocV (hp2 : p ≠ 2) :
    2 * Fintype.card (Commons.PaleyLocV p) + 1 = p := by
  have : Fintype.card (Commons.PaleyLocV p)
      = Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [this]
  exact card_sq hp2

lemma degree_paleyLoc (hp2 : p ≠ 2) (h4 : p % 4 = 1) (u : Commons.PaleyLocV p) :
    4 * ((Finset.univ.filter (fun v => Commons.paleyLocAdj p u v)).card) + 5 = p := by
  classical
  have hu : quadraticChar (ZMod p) (u : ZMod p) = 1 := (isNonzeroSq_iff _).mp u.2
  have hcard : (Finset.univ.filter (fun v : Commons.PaleyLocV p =>
        Commons.paleyLocAdj p u v)).card
      = ((Finset.univ : Finset (ZMod p)).filter
        (fun y => quadraticChar (ZMod p) y = 1 ∧
          quadraticChar (ZMod p) ((u : ZMod p) - y) = 1)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr ?_
    exact (Equiv.subtypeSubtypeEquivSubtypeInter (Commons.IsNonzeroSq (p := p))
        (fun y : ZMod p => Commons.IsNonzeroSq ((u : ZMod p) - y))).trans
      (Equiv.subtypeEquivRight (fun x => and_congr (isNonzeroSq_iff x) (isNonzeroSq_iff _)))
  rw [hcard]
  exact degree_count hp2 h4 _ hu


end Counts

section Paley


variable {p : ℕ} [NeZero p]

lemma paleyLoc_irrefl (u : Commons.PaleyLocV p) : ¬ Commons.paleyLocAdj p u u := by
  intro h
  exact h.1 (by simp [Commons.paleyLocAdj])

lemma paleyLoc_symm (hp : Nat.Prime p) (h4 : p % 4 = 1) (u v : Commons.PaleyLocV p) :
    Commons.paleyLocAdj p u v → Commons.paleyLocAdj p v u := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro h
  obtain ⟨hne, r, hr⟩ := h
  have hneg : IsSquare (-1 : ZMod p) := by
    refine ZMod.exists_sq_eq_neg_one_iff.mpr ?_
    omega
  obtain ⟨i, hi⟩ := hneg
  refine ⟨?_, ⟨i * r, ?_⟩⟩
  · intro hz
    apply hne
    have : ((u : ZMod p) - (v : ZMod p)) = -(((v : ZMod p) - (u : ZMod p))) := by ring
    rw [this, hz, neg_zero]
  · have h1 : ((v : ZMod p) - (u : ZMod p)) = (-1) * (((u : ZMod p) - (v : ZMod p))) := by ring
    rw [h1, hi, hr]; ring


theorem proof :
    ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p % 4 = 1 → 5 < p →
      ∀ (A R : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (c : ℝ),
        (∀ u v, Commons.paleyLocAdj p u v → A u v = 1) →
        (∀ u v, ¬ Commons.paleyLocAdj p u v → A u v = 0) →
        (∀ u, R u u = 0) →
        (∀ u v, Commons.paleyLocAdj p u v →
          R u v = (A * A) u v - (((p : ℝ) - 5) / 4) ^ 2 / (((p : ℝ) - 1) / 2)) →
        (c • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - R).PosSemidef →
        Commons.paleyLocTheta p hp.pos ≤ 2 + Real.sqrt ((p : ℝ) / 2 + 4 * c) := by
  classical
  intro p _ hp h4 hp5 A R c hA1 hA0 hRdiag hR hc
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set P : ℝ := (p : ℝ) with hP
  have hP5 : (5 : ℝ) < P := by rw [hP]; exact_mod_cast hp5
  set m : ℝ := (P - 1) / 2 with hm
  set d : ℝ := (P - 5) / 4 with hd
  -- the vertex count
  have hcardN : 2 * Fintype.card (Commons.PaleyLocV p) + 1 = p := card_paleyLocV hp2
  have hcard : (Fintype.card (Commons.PaleyLocV p) : ℝ) = m := by
    have : (2 : ℝ) * (Fintype.card (Commons.PaleyLocV p) : ℝ) + 1 = P := by
      rw [hP]; exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcardN
    rw [hm]; linarith
  -- the degree
  have hrow : ∀ u : Commons.PaleyLocV p, ∑ v, A u v = d := by
    intro u
    have hAv : ∀ v, A u v = (if Commons.paleyLocAdj p u v then (1 : ℝ) else 0) := by
      intro v
      by_cases h : Commons.paleyLocAdj p u v
      · rw [hA1 u v h, if_pos h]
      · rw [hA0 u v h, if_neg h]
    have hb : ∑ v, A u v
        = (((Finset.univ : Finset (Commons.PaleyLocV p)).filter
            (fun v => Commons.paleyLocAdj p u v)).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun v _ => hAv v)]
      exact Finset.sum_boole _ _
    have hdegN := degree_paleyLoc (p := p) hp2 h4 u
    have : (4 : ℝ) * (((Finset.univ : Finset (Commons.PaleyLocV p)).filter
        (fun v => Commons.paleyLocAdj p u v)).card : ℝ) + 5 = P := by
      rw [hP]; exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hdegN
    rw [hb, hd]; linarith
  have hne : Nonempty (Commons.PaleyLocV p) := by
    rw [← Fintype.card_pos_iff]
    have : (0 : ℝ) < (Fintype.card (Commons.PaleyLocV p) : ℝ) := by rw [hcard, hm]; linarith
    exact_mod_cast this
  have hS : Setup (Commons.paleyLocAdj p) A R m d c :=
    { hm := hcard.symm
      hsymm := paleyLoc_symm hp h4
      hirr := paleyLoc_irrefl
      hA1 := hA1
      hA0 := hA0
      hrow := hrow
      hRdiag := hRdiag
      hR := hR
      hc := hc }
  have hmain : Commons.thetaClique (Commons.paleyLocAdj p)
      ≤ (m / (m - d)) * (1 + Real.sqrt (d - d ^ 2 / m + c)) := thetaClique_le hS
  have hunfold : Commons.paleyLocTheta p hp.pos = Commons.thetaClique (Commons.paleyLocAdj p) :=
    rfl
  rw [hunfold]
  refine le_trans hmain ?_
  have hmd : m - d = (P + 3) / 4 := by rw [hm, hd]; ring
  have hmdpos : (0 : ℝ) < m - d := by rw [hmd]; linarith
  have hratio : m / (m - d) ≤ 2 := by rw [div_le_iff₀ hmdpos, hm, hmd]; linarith
  set K : ℝ := d - d ^ 2 / m + c with hK
  have hsq : (0 : ℝ) ≤ 1 + Real.sqrt K := by positivity
  have step1 : (m / (m - d)) * (1 + Real.sqrt K) ≤ 2 * (1 + Real.sqrt K) :=
    mul_le_mul_of_nonneg_right hratio hsq
  have hfour : Real.sqrt (4 * K) = 2 * Real.sqrt K := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    congr 1
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hKval : 4 * K = (P - 5) * (P + 3) / (2 * (P - 1)) + 4 * c := by
    rw [hK, hm, hd]
    have h1 : P - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hle : 4 * K ≤ P / 2 + 4 * c := by
    rw [hKval]
    have h1 : (0 : ℝ) < 2 * (P - 1) := by linarith
    have h2 : (P - 5) * (P + 3) / (2 * (P - 1)) ≤ P / 2 := by
      rw [div_le_div_iff₀ h1 (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  calc (m / (m - d)) * (1 + Real.sqrt K) ≤ 2 * (1 + Real.sqrt K) := step1
    _ = 2 + Real.sqrt (4 * K) := by rw [hfour]; ring
    _ ≤ 2 + Real.sqrt (P / 2 + 4 * c) := by
        have := Real.sqrt_le_sqrt hle
        linarith

end Paley

end Submissions.PaleyLocSecondMomentUnconditional.WoshuaJolk
