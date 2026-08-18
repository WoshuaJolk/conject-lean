import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Commons.PaleyLocalizationTheta

/-!
# Problem 26's upper half, reduced to one spectral quantity

Proof of `Statements.PaleyLocSecondMomentBound.statement`.

Part one is a general second-moment ceiling for the clique-theta of any regular graph, proved
here from scratch (a submission may not import another submission).  Part two instantiates it
at `Commons.paleyLocAdj p` and does the arithmetic.

**Part one.**  Let `X` be feasible for the program defining `Commons.thetaClique adj`, write
`⟪M, X⟫ = ∑ᵤ∑ᵥ Mᵤᵥ Xᵤᵥ` and `s = ∑ᵤ∑ᵥ Xᵤᵥ`.  Because `X` vanishes off the edges and the
diagonal, only the restriction of a test matrix there is ever seen, and three pairings are
forced: `⟪1, X⟫ = 1`, `⟪A, X⟫ = s - 1`, and `⟪A², X⟫ = d + ⟪R, X⟫ + (d²/m)(s-1)`.  With
`B = A - (d/m)J` one has `(B²)ᵤᵥ = (A²)ᵤᵥ - d²/m` entrywise, hence `⟪B, X⟫ = s(m-d)/m - 1`
and `⟪B², X⟫ = d - d²/m + ⟪R, X⟫`.  Cauchy–Schwarz in the semidefinite cone: with
`t = ⟪B, X⟫` the matrix `(B - t·1)²` is a square of a symmetric matrix, hence positive
semidefinite, hence `⟪(B - t·1)², X⟫ ≥ 0`; expanding and using `tr X = 1` gives
`t² ≤ ⟪B², X⟫`.  Finally `⟪R, X⟫ ≤ c` since `c·1 - R ⪰ 0`.

**Part two.**  `paleyLocAdj p` is irreflexive because `u - u = 0` is not a *nonzero* square,
and symmetric because `p ≡ 1 (mod 4)` makes `-1` a square, so `v - u = (-1)(u - v)` is a
nonzero square whenever `u - v` is.  Feeding `m = (p-1)/2` and `d = (p-5)/4` into part one
gives `2(p-1)/(p+3) · (1 + √((p-5)(p+3)/(8(p-1)) + c))`, and `2(p-1)/(p+3) ≤ 2` together with
`(p-5)(p+3)/(2(p-1)) ≤ p/2` weakens that to the stated `2 + √(p/2 + 4c)`.
-/

open scoped MatrixOrder Matrix
open Finset

namespace Submissions.PaleyLocSecondMomentBound.WoshuaJolk


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
        (Fintype.card (Commons.PaleyLocV p) : ℝ) = ((p : ℝ) - 1) / 2 →
        (∀ u v, Commons.paleyLocAdj p u v → A u v = 1) →
        (∀ u v, ¬ Commons.paleyLocAdj p u v → A u v = 0) →
        (∀ u, ∑ v, A u v = ((p : ℝ) - 5) / 4) →
        (∀ u, R u u = 0) →
        (∀ u v, Commons.paleyLocAdj p u v →
          R u v = (A * A) u v - (((p : ℝ) - 5) / 4) ^ 2 / (((p : ℝ) - 1) / 2)) →
        (c • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - R).PosSemidef →
        Commons.paleyLocTheta p hp.pos ≤ 2 + Real.sqrt ((p : ℝ) / 2 + 4 * c) := by
  intro p _ hp h4 hp5 A R c hcard hA1 hA0 hrow hRdiag hR hc
  set P : ℝ := (p : ℝ) with hP
  have hP5 : (5 : ℝ) < P := by rw [hP]; exact_mod_cast hp5
  set m : ℝ := (P - 1) / 2 with hm
  set d : ℝ := (P - 5) / 4 with hd
  have hne : Nonempty (Commons.PaleyLocV p) := by
    rw [← Fintype.card_pos_iff]
    have : (0 : ℝ) < (Fintype.card (Commons.PaleyLocV p) : ℝ) := by rw [hcard]; linarith
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
  -- arithmetic
  have hmd : m - d = (P + 3) / 4 := by rw [hm, hd]; ring
  have hmdpos : (0 : ℝ) < m - d := by rw [hmd]; linarith
  have hmpos : (0 : ℝ) < m := by rw [hm]; linarith
  have hratio : m / (m - d) ≤ 2 := by
    rw [div_le_iff₀ hmdpos, hm, hmd]; linarith
  set K : ℝ := d - d ^ 2 / m + c with hK
  have hsq : (0 : ℝ) ≤ 1 + Real.sqrt K := by positivity
  have step1 : (m / (m - d)) * (1 + Real.sqrt K) ≤ 2 * (1 + Real.sqrt K) := by
    exact mul_le_mul_of_nonneg_right hratio hsq
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

end Submissions.PaleyLocSecondMomentBound.WoshuaJolk
