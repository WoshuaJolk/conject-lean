import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Commons.PaleyLocalizationTheta

/-!
# Problem 26's lower half, from a certificate for the complement

Proof of `Statements.PaleyLocThetaLowerFromCertificate.statement`.

**The mechanism.**  Given `Ȳ` symmetric with unit diagonal, equal to `1` on every distinct
non-adjacent pair of `G_{p,1}`, and `θ̄·I - Ȳ ⪰ 0`, set `M = (θ̄·I - Ȳ) + J`.  Then

* `M ⪰ 0`, since it is a sum of two positive semidefinite matrices — `J = 𝟙𝟙ᵀ` is positive
  semidefinite because `xᵀJx = (∑ x)² ≥ 0`;
* `M u v = 0` for every distinct non-adjacent pair, since there `Ȳ u v = 1` and
  `(θ̄·I) u v = 0`, so `M u v = 0 - 1 + 1`;
* `tr M = θ̄m - m + m = θ̄m`, using `tr Ȳ = m` from the unit diagonal;
* `∑ᵤ∑ᵥ M u v ≥ m²`, since `∑ᵤ∑ᵥ (θ̄·I - Ȳ) u v = 𝟙ᵀ(θ̄I - Ȳ)𝟙 ≥ 0` and `∑ᵤ∑ᵥ J u v = m²`.

So `X = M/(θ̄m)` is feasible for the program defining `Commons.thetaClique (paleyLocAdj p)`
with objective at least `m/θ̄`.  The supremum is taken with `le_csSup`, which needs the
feasible set bounded above: for feasible `Z`, `𝟙ᵀZ𝟙 ≤ m · tr Z = m`, because `m·I - J ⪰ 0`
(that is Cauchy–Schwarz, `(∑x)² ≤ m∑x²`) and the trace of a product of positive semidefinite
matrices is nonnegative.

**The vertex count.**  `m = (p-1)/2` is proved rather than assumed: from `∑ₐ χ(a) = 0` for the
quadratic character `χ`, the nonzero squares and the non-squares are equinumerous, and there
are `p-1` of them together.

No vertex-transitivity and no orthonormal representations are used; this is the direction of
Lovász's `ϑ(G)ϑ(Ḡ) = n` that has a two-line matrix proof.
-/

open scoped MatrixOrder Matrix
open Finset

namespace Submissions.PaleyLocThetaLowerFromCertificate.WoshuaJolk

section General


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


section Lower

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma sum_sub' (M N : Matrix V V ℝ) :
    ∑ u, ∑ v, (M - N) u v = (∑ u, ∑ v, M u v) - ∑ u, ∑ v, N u v := by
  simp [Matrix.sub_apply, Finset.sum_sub_distrib]

lemma sum_add' (M N : Matrix V V ℝ) :
    ∑ u, ∑ v, (M + N) u v = (∑ u, ∑ v, M u v) + ∑ u, ∑ v, N u v := by
  simp [Matrix.add_apply, Finset.sum_add_distrib]

lemma sum_smul' (a : ℝ) (M : Matrix V V ℝ) :
    ∑ u, ∑ v, (a • M) u v = a * ∑ u, ∑ v, M u v := by
  simp [Matrix.smul_apply, Finset.mul_sum]

lemma sum_one' : ∑ u, ∑ v, (1 : Matrix V V ℝ) u v = (Fintype.card V : ℝ) := by
  simp [Matrix.one_apply, Finset.sum_ite_eq, Finset.card_univ]

lemma sum_allOnes' : ∑ u, ∑ v, (allOnes V) u v = (Fintype.card V : ℝ) ^ 2 := by
  simp [allOnes, Finset.card_univ, sq]

lemma allOnes_posSemidef : (allOnes V).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext u v; simp [Matrix.conjTranspose_apply]
  · intro x
    have hval : star x ⬝ᵥ ((allOnes V) *ᵥ x) = (∑ u, x u) * (∑ v, x v) := by
      simp only [Matrix.mulVec, dotProduct, allOnes, Matrix.of_apply, one_mul,
        Pi.star_apply, star_trivial, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [hval, ← sq]; positivity

lemma card_smul_one_sub_allOnes_psd :
    (((Fintype.card V : ℝ)) • (1 : Matrix V V ℝ) - allOnes V).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext u v
    by_cases h : u = v <;> simp [Matrix.conjTranspose_apply, h, allOnes, eq_comm, Matrix.one_apply]
  · intro x
    have hval : star x ⬝ᵥ ((((Fintype.card V : ℝ)) • (1 : Matrix V V ℝ) - allOnes V) *ᵥ x)
        = (Fintype.card V : ℝ) * (∑ u, x u ^ 2) - (∑ u, x u) ^ 2 := by
      simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul]
      congr 1
      · congr 1; simp [dotProduct, sq]
      · simp only [Matrix.mulVec, dotProduct, allOnes, Matrix.of_apply, one_mul,
          Pi.star_apply, star_trivial, Finset.mul_sum, Finset.sum_mul, sq]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [hval]
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := x)
    rw [Finset.card_univ] at h
    linarith

lemma sum_nonneg_of_psd {M : Matrix V V ℝ} (h : M.PosSemidef) : 0 ≤ ∑ u, ∑ v, M u v := by
  have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 (fun _ => (1:ℝ))
  simpa [Matrix.mulVec, dotProduct] using h2

lemma psd_smul {M : Matrix V V ℝ} (h : M.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    (a • M).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext u v
    simpa [Matrix.conjTranspose_apply] using congrArg (fun N : Matrix V V ℝ => a * N v u) h.1.eq.symm
  · intro x
    have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 x
    have he : star x ⬝ᵥ ((a • M) *ᵥ x) = a * (star x ⬝ᵥ (M *ᵥ x)) := by
      simp [Matrix.smul_mulVec, dotProduct_smul]
    rw [he]; exact mul_nonneg ha h2

lemma feasible_bddAbove (adj : V → V → Prop) :
    BddAbove (Commons.thetaCliqueFeasible adj) := by
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro s ⟨Z, hZ, htr, -, rfl⟩
  have h0 : 0 ≤ ip ((Fintype.card V : ℝ) • (1 : Matrix V V ℝ) - allOnes V) Z := by
    rw [ip_eq_trace (X_symm hZ)]
    exact trace_mul_nonneg card_smul_one_sub_allOnes_psd hZ
  have hA : ip (allOnes V) Z = ∑ u, ∑ v, Z u v := by
    simp only [ip, allOnes, Matrix.of_apply, one_mul]
  have hip : ip ((Fintype.card V : ℝ) • (1 : Matrix V V ℝ) - allOnes V) Z
      = (Fintype.card V : ℝ) * Z.trace - ∑ u, ∑ v, Z u v := by
    rw [ip_sub, ip_smul, ip_one hZ, hA]
  rw [hip, htr, mul_one] at h0
  linarith

/-- **Lower bound from a certificate for the complement.** -/
theorem thetaClique_ge (adj : V → V → Prop) (Ybar : Matrix V V ℝ) (m θ : ℝ)
    (hm : m = (Fintype.card V : ℝ)) (hmpos : 0 < m) (hθ : 0 < θ)
    (hdiag : ∀ u, Ybar u u = 1)
    (hnonadj : ∀ u v, u ≠ v → ¬ adj u v → Ybar u v = 1)
    (hpsd : (θ • (1 : Matrix V V ℝ) - Ybar).PosSemidef) :
    m / θ ≤ Commons.thetaClique adj := by
  classical
  set M : Matrix V V ℝ := (θ • (1 : Matrix V V ℝ) - Ybar) + allOnes V with hM
  have hMpsd : M.PosSemidef := hpsd.add allOnes_posSemidef
  have hscale : 0 < θ * m := mul_pos hθ hmpos
  set X : Matrix V V ℝ := (1 / (θ * m)) • M with hX
  have hXpsd : X.PosSemidef := psd_smul hMpsd (by positivity)
  have htrY : Ybar.trace = m := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hm]
  have htrA : (allOnes V).trace = m := by
    rw [Matrix.trace]; simp [allOnes, Finset.card_univ, hm]
  have htrM : M.trace = θ * m := by
    rw [hM, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, htrY, htrA,
      smul_eq_mul]
    rw [← hm]; ring
  have htrX : X.trace = 1 := by
    rw [hX, Matrix.trace_smul, smul_eq_mul, htrM]; field_simp
  have hzero : ∀ u v, u ≠ v → ¬ adj u v → X u v = 0 := by
    intro u v huv hadj
    rw [hX, hM]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply_ne huv, hnonadj u v huv hadj, smul_eq_mul]
    simp [allOnes]
  have hsumM : m ^ 2 ≤ ∑ u, ∑ v, M u v := by
    rw [hM, sum_add', sum_allOnes', ← hm]
    linarith [sum_nonneg_of_psd hpsd]
  have hobj : m / θ ≤ ∑ u, ∑ v, X u v := by
    rw [hX, sum_smul']
    have h1 : (0:ℝ) ≤ 1 / (θ * m) := by positivity
    have h2 : (1 / (θ * m)) * m ^ 2 ≤ (1 / (θ * m)) * ∑ u, ∑ v, M u v :=
      mul_le_mul_of_nonneg_left hsumM h1
    have h3 : (1 / (θ * m)) * m ^ 2 = m / θ := by field_simp
    linarith [h2, h3.ge, h3.le]
  exact le_trans hobj (le_csSup (feasible_bddAbove adj) ⟨X, hXpsd, htrX, hzero, rfl⟩)

end Lower


end General

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

theorem proof :
    ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p % 4 = 1 → 5 < p →
      ∀ (Ybar : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) (θ : ℝ),
        0 < θ →
        (∀ u, Ybar u u = 1) →
        (∀ u v, u ≠ v → ¬ Commons.paleyLocAdj p u v → Ybar u v = 1) →
        (θ • (1 : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ) - Ybar).PosSemidef →
        ((p : ℝ) - 1) / 2 / θ ≤ Commons.paleyLocTheta p hp.pos := by
  intro p _ hp h4 hp5 Ybar θ hθ hdiag hnonadj hpsd
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hcardN : 2 * Fintype.card (Commons.PaleyLocV p) + 1 = p := card_paleyLocV hp2
  have hP5 : (5 : ℝ) < (p : ℝ) := by exact_mod_cast hp5
  have hcard : ((p : ℝ) - 1) / 2 = (Fintype.card (Commons.PaleyLocV p) : ℝ) := by
    have h : (2 : ℝ) * (Fintype.card (Commons.PaleyLocV p) : ℝ) + 1 = (p : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcardN
    linarith
  have hmpos : (0 : ℝ) < ((p : ℝ) - 1) / 2 := by linarith
  have hne : Nonempty (Commons.PaleyLocV p) := by
    rw [← Fintype.card_pos_iff]
    have : (0 : ℝ) < (Fintype.card (Commons.PaleyLocV p) : ℝ) := by rw [← hcard]; linarith
    exact_mod_cast this
  have hunfold : Commons.paleyLocTheta p hp.pos = Commons.thetaClique (Commons.paleyLocAdj p) :=
    rfl
  rw [hunfold]
  exact thetaClique_ge (Commons.paleyLocAdj p) Ybar (((p : ℝ) - 1) / 2) θ hcard hmpos hθ
    hdiag hnonadj hpsd

end Paley

end Submissions.PaleyLocThetaLowerFromCertificate.WoshuaJolk
