import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.LinearCombination

/-!
# KontsevichPhiAperiodic — an explicit exact solution of Zharkov's system off the torus

Witness for `Statements.KontsevichPhiAperiodic.statement`.

## The construction in one line

Write `Λ(x,u) = x ∧ u ∈ Γ_p ⊗ ⋀²Γ₂` (`lam` below), `⟨·,·⟩` for the standard inner product on
`Γ₂` (`ip`), and `β ⌟ u` for the contraction of a bivector with `u` (`kap` on basis
bivectors).  Then

  `Φ_{x,u}(β)  =  - Λ(x,u) · Λ(x, (β ⌟ u) / ⟨u,u⟩)`.

Linearity in `β` is immediate from the formula; invariance under `u ↦ m u` is immediate
because numerator and denominator are both homogeneous of degree `2` in `u`; and `⟨u,u⟩ = 0`
only for `u = 0`, where `Λ(x,u) = 0` makes the formula `0` anyway, so no case split is needed
in the statement.

## Why it works

Two computations, both pure algebra, both done in `key`, `key2`, `key3` and then `ring`.

*Evaluation.*  `∑_k (u ∧ v)_k (ê_k ⌟ u) = ⟨u,u⟩ v - ⟨u,v⟩ u` (`kap_sum`, four polynomial
identities in eight integer variables).  Hence

  `Φ_{x,u}(u ∧ v) = - Λ(x,u) Λ(x,v) + (⟨u,v⟩/⟨u,u⟩) Λ(x,u)²`.

The first term is the whole content; the second is a correction whose only job is to make the
map vanish at `v = u`, which is exactly what linearity in `β` demands, and which is invisible
to both relations because it cancels in pairs.

*Translation.*  `Λ(x + u⊗s, y) = Λ(x,y) + s·(u ∧ y)` (`lam_add_outer`).  In particular
`Λ(·,u)` is invariant along its own direction.  Writing `a = Λ(x,u)`, `b = Λ(x,v)`,
`S = parPoly s`, `W = u ∧ v`, the six triangle terms and the eight parallelogram terms
collapse to `S²W²` and `2STW²` respectively, and the `⟨u,v⟩/⟨u,u⟩` corrections cancel
identically: in the triangle they appear once with each sign at each of the three lines
`u`, `v`, `u - v`; in the parallelogram the two squares `Λ(·,u)²` and `Λ(·,v)²` take equal
values at the two `+` and the two `−` vertices.

## What this does and does not say

**Says.**  Zharkov's equations (1) and (2), read as a system of equations on a family `Φ`
indexed by a *vector space* of vertices, are consistent — exactly, with no sublattice `L`
needed, at every pair of directions and not only at primitive ones.  Combined with
`KontsevichPhiSoundness` at `L = ⊥`, every balanced chain has tautological class `0`.

**Does not say.**  Nothing about `Γ₁`-periodicity, which is the requirement the root statement
makes and this one drops, and which `Φ` above visibly fails: `Λ(x + g, u) = Λ(x,u) + Λ(g,u)`,
and `Λ(g,u) ≠ 0` for `g ∈ Γ₁`.  Nothing about `θ`, `w₁`, `w₂`, the lattice `L`, tropical
cycles, or the Hodge conjecture.  In particular this is *not* a solution of the root
statement and does not claim to be.

**Control.**  `zero_family_fails` at the end checks that the relations are not vacuous: the
zero family has triangle defect `-a²x₁₂² ≠ 0` at one explicit instance.  Had that evaluated
to zero, `Φ ≡ 0` would have witnessed the statement and it would have said nothing.
-/

namespace Submissions.KontsevichPhiAperiodic.Explicit

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

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

noncomputable def rowPoly (A : G2P) (i : Fin 4) : T := ∑ m : Fin 4, ((A i m : ℤ) : ℚ) • pv m

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

abbrev statement : Prop :=
  ∃ Φ : G2P → G2 → Fin 6 → T,
    (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Φ x (m • u) = Φ x u) ∧
    (∀ (x : G2P) (s : Gp) (u v : G2), triDefect Φ x s u v = 0) ∧
    (∀ (x : G2P) (s t : Gp) (u v : G2), parDefect Φ x s t u v = 0)

/-! ## The construction -/

/-- `Λ(x,u) = x ∧ u ∈ Γ_p ⊗ ⋀²Γ₂`, of bidegree `(1,1)`. -/
noncomputable def lam (x : G2P) (u : G2) : T :=
  ∑ l : Fin 6,
    (C ((u (bivSnd l) : ℤ) : ℚ) * rowPoly x (bivFst l)
      - C ((u (bivFst l) : ℤ) : ℚ) * rowPoly x (bivSnd l)) * bv l

/-- The standard inner product on `Γ₂`. -/
def ip (u v : G2) : ℤ := ∑ i : Fin 4, u i * v i

/-- `ê_k ⌟ u`, the contraction of the `k`-th basis bivector with `u`. -/
def kap (u : G2) (k : Fin 6) : G2 := fun j =>
  (if j = bivSnd k then u (bivFst k) else 0) - (if j = bivFst k then u (bivSnd k) else 0)

/-- The candidate `Φ`. -/
noncomputable def Phi (x : G2P) (u : G2) (k : Fin 6) : T :=
  -(C (((ip u u : ℤ) : ℚ))⁻¹ * (lam x u * lam x (kap u k)))

/-! ## Linearity of `lam` -/

lemma lam_add (x : G2P) (u v : G2) : lam x (u + v) = lam x u + lam x v := by
  simp only [lam, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.add_apply, Int.cast_add, map_add]
  ring

lemma lam_zsmul (x : G2P) (m : ℤ) (u : G2) : lam x (m • u) = C ((m : ℚ)) * lam x u := by
  simp only [lam, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, map_mul]
  ring

lemma lam_zero (x : G2P) : lam x (0 : G2) = 0 := by
  simp [lam]

lemma lam_sub (x : G2P) (u v : G2) : lam x (u - v) = lam x u - lam x v := by
  simp only [lam, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.sub_apply, Int.cast_sub, map_sub]
  ring

lemma lam_fin_sum (x : G2P) (f : Fin 6 → G2) :
    lam x (∑ k : Fin 6, f k) = ∑ k : Fin 6, lam x (f k) := by
  simp only [Fin.sum_univ_six, lam_add]

@[simp] lemma bF0 : bivFst 0 = 0 := rfl
@[simp] lemma bF1 : bivFst 1 = 0 := rfl
@[simp] lemma bF2 : bivFst 2 = 0 := rfl
@[simp] lemma bF3 : bivFst 3 = 1 := rfl
@[simp] lemma bF4 : bivFst 4 = 1 := rfl
@[simp] lemma bF5 : bivFst 5 = 2 := rfl
@[simp] lemma bS0 : bivSnd 0 = 1 := rfl
@[simp] lemma bS1 : bivSnd 1 = 2 := rfl
@[simp] lemma bS2 : bivSnd 2 = 3 := rfl
@[simp] lemma bS3 : bivSnd 3 = 2 := rfl
@[simp] lemma bS4 : bivSnd 4 = 3 := rfl
@[simp] lemma bS5 : bivSnd 5 = 3 := rfl

/-! ## The contraction identity -/

lemma kap_sum (u v : G2) :
    (∑ k : Fin 6, wedge u v k • kap u k) = ip u u • v - ip u v • u := by
  funext j
  have hl : (∑ k : Fin 6, wedge u v k • kap u k) j = ∑ k : Fin 6, wedge u v k * kap u k j := by
    simp [Finset.sum_apply]
  rw [hl]
  fin_cases j <;>
    simp [wedge, kap, ip, Fin.sum_univ_six, Fin.sum_univ_four, Fin.ext_iff] <;> ring

/-! ## `wedge` identities -/

lemma wedge_swap (u v : G2) : wedge u v = fun k => -(wedge v u k) := by
  funext k; simp only [wedge]; ring

lemma wedge_sub_left (u v : G2) : wedge u v = wedge (u - v) v := by
  funext k; simp only [wedge, Pi.sub_apply]; ring

lemma wedgePoly_self (u : G2) : wedgePoly u u = 0 := by
  simp only [wedgePoly, wedge]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : u (bivFst k) * u (bivSnd k) - u (bivSnd k) * u (bivFst k) = 0 := by ring
  rw [this]; simp

lemma wedgePoly_swap (u v : G2) : wedgePoly v u = - wedgePoly u v := by
  simp only [wedgePoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wedge]
  rw [← neg_smul]
  congr 1
  push_cast
  ring

lemma wedgePoly_sub_right (u v w : G2) :
    wedgePoly u (v - w) = wedgePoly u v - wedgePoly u w := by
  simp only [wedgePoly, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wedge, Pi.sub_apply]
  rw [← sub_smul]
  congr 1
  push_cast
  ring

/-! ## Behaviour of `lam` under translation -/

lemma rowPoly_add_outer (x : G2P) (u : G2) (s : Gp) (i : Fin 4) :
    rowPoly (x + outer u s) i = rowPoly x i + C ((u i : ℤ) : ℚ) * parPoly s := by
  simp only [rowPoly, outer, parPoly, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Int.cast_add, Int.cast_mul, smul_eq_C_mul, map_add, map_mul]
  ring

lemma lam_add_outer (x : G2P) (u : G2) (s : Gp) (y : G2) :
    lam (x + outer u s) y = lam x y + parPoly s * wedgePoly u y := by
  simp only [lam, rowPoly_add_outer, wedgePoly, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [wedge, smul_eq_C_mul, Int.cast_sub, Int.cast_mul, map_sub, map_mul]
  ring

/-! ## The evaluation formula for `Phi` -/

lemma app_neg (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) :
    app Φ x u (fun k => -(β k)) = -(app Φ x u β) := by
  simp only [app, Int.cast_neg, neg_smul, ← Finset.sum_neg_distrib]

lemma app_Phi (x : G2P) (u : G2) (β : Fin 6 → ℤ) :
    app Phi x u β
      = -(C (((ip u u : ℤ) : ℚ))⁻¹ * (lam x u * lam x (∑ k : Fin 6, β k • kap u k))) := by
  rw [lam_fin_sum]
  simp only [app, Phi, smul_eq_C_mul, lam_zsmul, Fin.sum_univ_six]
  ring

lemma ip_self_eq_zero {u : G2} (h : ip u u = 0) : u = 0 := by
  funext i
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ u i * u i := fun i _ => mul_self_nonneg _
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp h2

lemma lam_of_ip_zero (x : G2P) {u : G2} (h : ip u u = 0) : lam x u = 0 := by
  have hu : u = 0 := ip_self_eq_zero h
  subst hu
  exact lam_zero x

/-- The scalar `⟨u,v⟩ / ⟨u,u⟩`. -/
noncomputable def cc (u v : G2) : T := C (((ip u v : ℤ) : ℚ) * (((ip u u : ℤ) : ℚ))⁻¹)

/-- The master evaluation: `Φ_{x,u}(u ∧ v) = -Λ(x,u)Λ(x,v) + (⟨u,v⟩/⟨u,u⟩) Λ(x,u)²`. -/
lemma key (x : G2P) (u v : G2) :
    app Phi x u (wedge u v)
      = -(lam x u * lam x v) + cc u v * (lam x u * lam x u) := by
  rw [app_Phi, kap_sum, lam_sub, lam_zsmul, lam_zsmul, cc, map_mul]
  by_cases h : ip u u = 0
  · rw [lam_of_ip_zero x h]; ring
  · have hq : ((ip u u : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h
    have hc : C ((((ip u u : ℤ) : ℚ))⁻¹) * C (((ip u u : ℤ) : ℚ)) = (1 : T) := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    linear_combination (-(lam x u * lam x v)) * hc

lemma key2 (x : G2P) (u v : G2) :
    app Phi x v (wedge u v)
      = lam x v * lam x u - cc v u * (lam x v * lam x v) := by
  rw [wedge_swap, app_neg, key]
  ring

lemma key3 (x : G2P) (u v : G2) :
    app Phi x (u - v) (wedge u v)
      = -(lam x (u - v) * lam x v) + cc (u - v) v * (lam x (u - v) * lam x (u - v)) := by
  rw [wedge_sub_left u v, key]

/-! ## Scale invariance -/

lemma kap_smul (m : ℤ) (u : G2) (k : Fin 6) : kap (m • u) k = m • kap u k := by
  funext j
  simp only [kap, Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero, mul_sub]

lemma ip_smul_self (m : ℤ) (u : G2) : ip (m • u) (m • u) = m ^ 2 * ip u u := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma Phi_smul (x : G2P) (u : G2) (m : ℤ) (hm : m ≠ 0) : Phi x (m • u) = Phi x u := by
  funext k
  have hm' : ((m : ℚ)) ≠ 0 := by exact_mod_cast hm
  have hm2 : ((m : ℚ)) ^ 2 ≠ 0 := pow_ne_zero 2 hm'
  simp only [Phi, ip_smul_self, kap_smul, lam_zsmul]
  have hscal : ((((m ^ 2 * ip u u : ℤ)) : ℚ))⁻¹ * ((m : ℚ) * (m : ℚ))
      = (((ip u u : ℤ) : ℚ))⁻¹ := by
    push_cast
    rw [mul_inv, show ((m : ℚ) * (m : ℚ)) = (m : ℚ) ^ 2 by ring, mul_right_comm,
      inv_mul_cancel₀ hm2, one_mul]
  have hC : (C ((((m ^ 2 * ip u u : ℤ)) : ℚ))⁻¹ : T) * (C ((m : ℚ)) * C ((m : ℚ)))
      = (C (((ip u u : ℤ) : ℚ))⁻¹ : T) := by
    rw [← map_mul, ← map_mul, hscal]
  linear_combination (-(lam x u * lam x (kap u k))) * hC

/-! ## The main theorem -/

theorem proof : statement := by
  refine ⟨Phi, fun x u m hm => Phi_smul x u m hm, ?_, ?_⟩
  · intro x s u v
    have hA : wedgePoly u u = 0 := wedgePoly_self u
    have hB : wedgePoly v v = 0 := wedgePoly_self v
    have hCC : wedgePoly v u = - wedgePoly u v := wedgePoly_swap u v
    simp only [triDefect, key, key2, key3, lam_add_outer, lam_sub, hA, hB, hCC]
    ring
  · intro x s t u v
    have hA : wedgePoly u u = 0 := wedgePoly_self u
    have hB : wedgePoly v v = 0 := wedgePoly_self v
    have hCC : wedgePoly v u = - wedgePoly u v := wedgePoly_swap u v
    have h2 : (C (2 : ℚ) : T) = 2 := map_ofNat C 2
    simp only [parDefect, key, key2, lam_add_outer, hA, hB, hCC, smul_eq_C_mul, h2]
    ring

/-- **Non-vacuity control.**  The relations are not satisfied by the zero family: at
`x = 0`, `s = a`, `u = e₁`, `v = e₂` the triangle defect of `Φ ≡ 0` is `-a²x₁₂² ≠ 0`.
Had this evaluated to `0` the statement would have been trivially witnessed by `Φ ≡ 0`
and would have said nothing. -/
lemma zero_family_fails :
    triDefect (fun _ _ _ => (0 : T)) (0 : G2P) ![1, 0, 0, 0] ![1, 0, 0, 0] ![0, 1, 0, 0]
      ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) h
  simp [triDefect, app, parPoly, wedgePoly, pv, bv, wedge, bivFst, bivSnd,
    Fin.sum_univ_four, Fin.sum_univ_six] at h2

end Submissions.KontsevichPhiAperiodic.Explicit



