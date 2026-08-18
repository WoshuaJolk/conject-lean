import Mathlib

/-!
# An exact closed-form solution of Kontsevich's triangle and parallelogram system

Dropping only the `Γ₁`-periodicity requirement, Zharkov's equations (1) and (2) are solvable
with zero defect, by

  `Φ_{x,u}(β) = - β̂ · W(x,u) · σ_u(x)`,

where `β̂` is `β` read as a linear form in the `⋀²Γ₂` coordinates, `W(x,u)` is the projection
of `x ∧ u ∈ ⋀²Γ₂ ⊗ Γ_p` to bidegree `(1,1)`, and `σ_u = u/⟨u,u⟩` is the unique multiple of `u`
in `Γ₂^* ⊗ ℚ` pairing to `1` with `u` (so `σ_{mu} = σ_u/m`, which is what makes `Φ` descend to
`P(Γ₂ ⊗ ℚ)`).

The verification needs only five facts, and no expansion in coordinates:

* `W` is additive in `x` and additive in `u`;
* `W(u ⊗ s, v) = ŝ · (u ∧ v)^`, hence `W(u ⊗ s, u) = 0`;
* `σ_u` is additive in `x`;
* `σ_u(u ⊗ s) = ŝ` when `u ≠ 0`;
* `u ∧ v = 0` whenever `u = 0`, `v = 0` or `u = v`, which handles the degenerate cases.
-/

namespace Submissions.KontsevichPhiExactNoPeriod.ExactSolution

open MvPolynomial

abbrev T : Type := MvPolynomial (Fin 10) ℚ

noncomputable def pv : Fin 4 → T := ![X 0, X 1, X 2, X 3]
noncomputable def bv : Fin 6 → T := ![X 4, X 5, X 6, X 7, X 8, X 9]

abbrev G2 : Type := Fin 4 → ℤ
abbrev Gp : Type := Fin 4 → ℤ
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

def bivFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def bivSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

def wedge (u v : G2) (k : Fin 6) : ℤ :=
  u (bivFst k) * v (bivSnd k) - u (bivSnd k) * v (bivFst k)

noncomputable def wedgePoly (u v : G2) : T := ∑ k : Fin 6, ((wedge u v k : ℤ) : ℚ) • bv k

noncomputable def parPoly (s : Gp) : T := ∑ k : Fin 4, ((s k : ℤ) : ℚ) • pv k

def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

noncomputable def app (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) : T :=
  ∑ k : Fin 6, ((β k : ℤ) : ℚ) • Φ x u k

noncomputable def triDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) (u - v) (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    + app Φ (x + outer v s) v (wedge u v)
    - app Φ (x + outer v s) (u - v) (wedge u v)
    - parPoly s ^ 2 * wedgePoly u v ^ 2

noncomputable def parDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s t : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) v (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    - app Φ (x + outer v t) u (wedge u v)
    + app Φ (x + outer v t) v (wedge u v)
    + app Φ (x + outer u s + outer v t) u (wedge u v)
    - app Φ (x + outer u s + outer v t) v (wedge u v)
    - (2 : ℚ) • (parPoly s * parPoly t * wedgePoly u v ^ 2)

/-! ### The witness -/

/-- The `i`-th row of `x ∈ Γ₂ ⊗ Γ_p`, read as a linear form in the parameters. -/
noncomputable def rowP (x : G2P) (i : Fin 4) : T := ∑ m : Fin 4, ((x i m : ℤ) : ℚ) • pv m

/-- `W(x,u)`: the projection of `x ∧ u ∈ ⋀²Γ₂ ⊗ Γ_p` to `Γ_p ⊗ ⋀²Γ₂`. -/
noncomputable def Wm (x : G2P) (u : G2) : T :=
  ∑ k : Fin 6,
    (((u (bivSnd k) : ℤ) : ℚ) • rowP x (bivFst k)
      - ((u (bivFst k) : ℤ) : ℚ) • rowP x (bivSnd k)) * bv k

/-- `⟨u,u⟩`, the normalising scalar for `σ_u`. -/
def nrm (u : G2) : ℤ := ∑ i : Fin 4, u i * u i

/-- `σ_u(x)`, where `σ_u = u/⟨u,u⟩ ∈ Γ₂^* ⊗ ℚ` is the multiple of `u` with `σ_u(u) = 1`. -/
noncomputable def sg (x : G2P) (u : G2) : T :=
  ((nrm u : ℤ) : ℚ)⁻¹ • ∑ i : Fin 4, ((u i : ℤ) : ℚ) • rowP x i

/-- The witness. -/
noncomputable def PhiE : G2P → G2 → Fin 6 → T := fun x u k => -(bv k * (Wm x u * sg x u))

/-! ### Elementary lemmas -/

lemma rowP_add (x y : G2P) (i : Fin 4) : rowP (x + y) i = rowP x i + rowP y i := by
  simp only [rowP, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  rw [add_smul]

lemma rowP_outer (u : G2) (s : Gp) (i : Fin 4) :
    rowP (outer u s) i = ((u i : ℤ) : ℚ) • parPoly s := by
  simp only [rowP, outer, parPoly, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  rw [smul_smul]

lemma Wm_add_left (x y : G2P) (u : G2) : Wm (x + y) u = Wm x u + Wm y u := by
  simp only [Wm, rowP_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_add, smul_add]
  ring

lemma Wm_sub_right (x : G2P) (u v : G2) : Wm x (u - v) = Wm x u - Wm x v := by
  simp only [Wm, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rw [sub_smul, sub_smul]
  ring

lemma wedge_self (u : G2) : wedge u u = 0 := by
  funext k; simp [wedge]; ring

lemma wedge_left_zero (v : G2) : wedge 0 v = 0 := by
  funext k; simp [wedge]

lemma wedge_right_zero (u : G2) : wedge u 0 = 0 := by
  funext k; simp [wedge]

lemma wedgePoly_self (u : G2) : wedgePoly u u = 0 := by
  simp [wedgePoly, wedge_self]

lemma wedge_sub_right (u v : G2) : wedge u (u - v) = fun k => -(wedge u v k) := by
  funext k; simp only [wedge, Pi.sub_apply]; ring

lemma wedge_sub_right' (u v : G2) : wedge v (u - v) = fun k => -(wedge u v k) := by
  funext k; simp only [wedge, Pi.sub_apply]; ring

lemma wedgePoly_sub_right (u v : G2) : wedgePoly u (u - v) = -wedgePoly u v := by
  simp only [wedgePoly, wedge_sub_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; rw [neg_smul]

lemma wedgePoly_sub_right' (u v : G2) : wedgePoly v (u - v) = -wedgePoly u v := by
  simp only [wedgePoly, wedge_sub_right', ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; rw [neg_smul]

lemma Wm_outer (u : G2) (s : Gp) (v : G2) : Wm (outer u s) v = parPoly s * wedgePoly u v := by
  simp only [Wm, rowP_outer, wedgePoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_smul, ← sub_smul, smul_mul_assoc, mul_smul_comm]
  congr 1
  · simp only [wedge]; push_cast; ring

lemma Wm_outer_self (u : G2) (s : Gp) : Wm (outer u s) u = 0 := by
  rw [Wm_outer, wedgePoly_self, mul_zero]

lemma sg_add_left (x y : G2P) (u : G2) : sg (x + y) u = sg x u + sg y u := by
  simp only [sg, rowP_add]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_add]

lemma outer_sub_left (u v : G2) (s : Gp) : outer u s - outer v s = outer (u - v) s := by
  funext i m; simp [outer]; ring

lemma nrm_ne_zero {u : G2} (hu : u ≠ 0) : ((nrm u : ℤ) : ℚ) ≠ 0 := by
  have h : nrm u ≠ 0 := by
    intro h
    apply hu
    funext i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ u j * u j := fun j _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
    simpa using mul_self_eq_zero.1 this
  exact_mod_cast h

lemma sg_outer_self {u : G2} (hu : u ≠ 0) (s : Gp) : sg (outer u s) u = parPoly s := by
  simp only [sg, rowP_outer]
  have : ∑ i : Fin 4, ((u i : ℤ) : ℚ) • (((u i : ℤ) : ℚ) • parPoly s)
      = ((nrm u : ℤ) : ℚ) • parPoly s := by
    simp only [smul_smul, ← Finset.sum_smul, nrm]
    congr 1
    push_cast
    ring
  rw [this, smul_smul, inv_mul_cancel₀ (nrm_ne_zero hu), one_smul]

/-! ### `app` of the witness -/

noncomputable def bvv (β : Fin 6 → ℤ) : T := ∑ k : Fin 6, ((β k : ℤ) : ℚ) • bv k

lemma app_PhiE (x : G2P) (u : G2) (β : Fin 6 → ℤ) :
    app PhiE x u β = -(bvv β * (Wm x u * sg x u)) := by
  simp only [app, PhiE, bvv, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_neg, smul_mul_assoc]

lemma bvv_wedge (u v : G2) : bvv (wedge u v) = wedgePoly u v := rfl

/-! ### Degenerate case -/

lemma app_of_wedge_zero (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u v w : G2)
    (h : wedge u v = 0) : app Φ x w (wedge u v) = 0 := by
  simp [app, h]

lemma wedgePoly_of_wedge_zero {u v : G2} (h : wedge u v = 0) : wedgePoly u v = 0 := by
  simp [wedgePoly, h]

/-! ### The two verifications -/

lemma sg_scale (x : G2P) (u : G2) {m : ℤ} (hm : m ≠ 0) :
    sg x (m • u) = ((m : ℚ))⁻¹ • sg x u := by
  have hmq : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 hm
  simp only [sg, Pi.smul_apply, smul_eq_mul]
  have h1 : nrm (m • u) = m * m * nrm u := by
    simp only [nrm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have h2 : ∑ i : Fin 4, (((m * u i : ℤ)) : ℚ) • rowP x i
      = (m : ℚ) • ∑ i : Fin 4, ((u i : ℤ) : ℚ) • rowP x i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [smul_smul]
  simp only [h1, h2, smul_smul]
  congr 1
  push_cast
  field_simp

lemma Wm_scale (x : G2P) (u : G2) (m : ℤ) : Wm x (m • u) = (m : ℚ) • Wm x u := by
  simp only [Wm, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rw [mul_smul, mul_smul, ← smul_sub, smul_mul_assoc]

theorem phi_scale_inv (x : G2P) (u : G2) (m : ℤ) (hm : m ≠ 0) : PhiE x (m • u) = PhiE x u := by
  have hmq : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 hm
  funext k
  simp only [PhiE, Wm_scale, sg_scale x u hm]
  congr 2
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hmq, one_smul]

/-- The `Φ`-side rewriting used by both verifications. -/
lemma app_at (u v w : G2) (y : G2P) :
    app PhiE y w (wedge u v) = -(wedgePoly u v * (Wm y w * sg y w)) := by
  rw [app_PhiE, bvv_wedge]

theorem tri_zero (x : G2P) (s : Gp) (u v : G2) : triDefect PhiE x s u v = 0 := by
  by_cases hw : wedge u v = 0
  · simp only [triDefect, app_of_wedge_zero PhiE _ u v _ hw, wedgePoly_of_wedge_zero hw]
    ring
  · have hu : u ≠ 0 := by rintro rfl; exact hw (wedge_left_zero v)
    have hv : v ≠ 0 := by rintro rfl; exact hw (wedge_right_zero u)
    have huv : u - v ≠ 0 := by
      intro h
      have huv' : u = v := by
        funext i
        have hi := congrFun h i
        simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hi
        exact hi
      exact hw (huv' ▸ wedge_self v)
    have hAA : (outer u s - outer v s) + outer v s = outer u s := by abel
    have hsg1 := sg_add_left (outer u s - outer v s) (outer v s) (u - v)
    rw [hAA, outer_sub_left, sg_outer_self huv s] at hsg1
    -- hsg1 : sg (outer u s) (u-v) = parPoly s + sg (outer v s) (u-v)
    have hWx : Wm x u = Wm x v + Wm x (u - v) := by
      rw [Wm_sub_right]; ring
    simp only [triDefect, app_at, Wm_add_left, sg_add_left,
      Wm_outer_self, Wm_outer, wedgePoly_sub_right, wedgePoly_sub_right',
      sg_outer_self hu s, sg_outer_self hv s, hsg1, hWx]
    ring

theorem par_zero (x : G2P) (s t : Gp) (u v : G2) : parDefect PhiE x s t u v = 0 := by
  by_cases hw : wedge u v = 0
  · simp only [parDefect, app_of_wedge_zero PhiE _ u v _ hw, wedgePoly_of_wedge_zero hw]
    rw [two_smul]; ring
  · have hu : u ≠ 0 := by rintro rfl; exact hw (wedge_left_zero v)
    have hv : v ≠ 0 := by rintro rfl; exact hw (wedge_right_zero u)
    have hvu : wedgePoly v u = -wedgePoly u v := by
      simp only [wedgePoly, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : wedge v u k = -(wedge u v k) := by simp only [wedge]; ring
      rw [this]; push_cast; rw [neg_smul]
    simp only [parDefect, app_at, Wm_add_left, sg_add_left,
      Wm_outer_self, Wm_outer, hvu, sg_outer_self hu s, sg_outer_self hv t]
    rw [two_smul]
    ring

/-- Kontsevich's system minus `Γ₁`-periodicity, solved exactly. -/
theorem proof :
    ∃ Φ : G2P → G2 → Fin 6 → T,
      (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Φ x (m • u) = Φ x u) ∧
      (∀ (x : G2P) (s : Gp) (u v : G2), triDefect Φ x s u v = 0) ∧
      (∀ (x : G2P) (s t : Gp) (u v : G2), parDefect Φ x s t u v = 0) :=
  ⟨PhiE, fun x u m hm => phi_scale_inv x u m hm, tri_zero, par_zero⟩

end Submissions.KontsevichPhiExactNoPeriod.ExactSolution
