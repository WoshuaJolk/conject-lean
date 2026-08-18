import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin

namespace Submissions.EigenwaveKernelPolarisation.LemmaA

open ExteriorAlgebra

open ExteriorAlgebra

/-- `Γ₁ ⊕ (Γ₂ ⊗ ℚ)`, both of rank `N`.  The first factor carries the `γ` basis of the period
lattice, the second the `e` basis of `Γ₂`. -/
abbrev W (N : ℕ) : Type := (Fin N → ℚ) × (Fin N → ℚ)

/-- The exterior algebra `⋀(Γ₁ ⊕ Γ₂ ⊗ ℚ)`.  Its `(q,r)` graded piece is `⋀^q Γ₁ ⊗ ⋀^r Γ₂`,
embedded as the span of the products `γ_{i₁} ⋯ γ_{i_q} · e_{j₁} ⋯ e_{j_r}`. -/
abbrev EA (N : ℕ) : Type := ExteriorAlgebra ℚ (W N)

/-- The square-zero extension of `EA N` by itself, used to build `φ` as a derivation. -/
abbrev TS (N : ℕ) : Type := TrivSqZeroExt (EA N) (EA N)

/-- `Q̃ : Γ₁ ⊕ Γ₂ → Γ₁ ⊕ Γ₂`, `γ ↦ Qγ ∈ Γ₂` and `e ↦ 0`.  On the basis, `γ_i ↦ Q_{·,i}`, the
`i`-th column of `Q` read in the `e`-basis — Zharkov's identification of `Γ₁` inside
`Γ₂ ⊗ ℝ`. -/
noncomputable def qmap {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) : W N →ₗ[ℚ] W N :=
  (LinearMap.inr ℚ _ _).comp ((Matrix.mulVecLin Q).comp (LinearMap.fst ℚ _ _))

/-- `w ↦ ι w + ε · ι (Q̃ w)` into the square-zero extension. -/
noncomputable def Fmap {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) : W N →ₗ[ℚ] TS N where
  toFun w := TrivSqZeroExt.inl (ι ℚ w) + TrivSqZeroExt.inr (ι ℚ (qmap Q w))
  map_add' x y := by simp [map_add]; abel
  map_smul' r x := by simp [map_smul]

/-- The image of every vector squares to zero, because `ι x · ι y + ι y · ι x = 0`. -/
theorem Fmap_sq {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (w : W N) : Fmap Q w * Fmap Q w = 0 := by
  apply TrivSqZeroExt.ext
  · simp [Fmap, TrivSqZeroExt.fst_mul]
  · simp [Fmap, TrivSqZeroExt.snd_mul, ExteriorAlgebra.ι_add_mul_swap]

/-- The algebra map `⋀W → EA N ⋉ EA N` whose second component is the derivation `φ`. -/
noncomputable def Lift {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) : EA N →ₐ[ℚ] TS N :=
  ExteriorAlgebra.lift ℚ ⟨Fmap Q, Fmap_sq Q⟩

/-- **The eigenwave operator** `φ`: the even derivation of `⋀(Γ₁ ⊕ Γ₂)` extending `γ ↦ Qγ`,
`e ↦ 0`.  See the module docstring for the sign convention. -/
noncomputable def phi {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) : EA N →+ EA N where
  toFun x := (Lift Q x).snd
  map_zero' := by simp
  map_add' x y := by simp [map_add]

theorem lift_fst {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (x : EA N) : (Lift Q x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℚ (EA N) (EA N)).comp (Lift Q) = AlgHom.id ℚ (EA N) := by
    apply ExteriorAlgebra.hom_ext; apply LinearMap.ext; intro w; simp [Lift, Fmap]
  exact congrArg (fun f => f x) (congrArg (fun (f : EA N →ₐ[ℚ] EA N) => (f : EA N → EA N)) h)

/-- `φ(ι w) = ι (Q̃ w)`. -/
theorem phi_iota {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (w : W N) :
    phi Q (ι ℚ w) = ι ℚ (qmap Q w) := by simp [phi, Lift, Fmap]

/-- **Leibniz.**  `φ` is an even derivation: `φ(xy) = x φ(y) + φ(x) y`. -/
theorem phi_mul {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (x y : EA N) :
    phi Q (x * y) = x * phi Q y + phi Q x * y := by
  simp [phi, map_mul, TrivSqZeroExt.snd_mul, lift_fst]

theorem phi_one {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) : phi Q 1 = 0 := by simp [phi]

/-- `γ_i ∈ Γ₁`. -/
def gam {N : ℕ} (i : Fin N) : W N := (Pi.single i 1, 0)

/-- `e_i ∈ Γ₂`. -/
def eb {N : ℕ} (i : Fin N) : W N := (0, Pi.single i 1)

/-- The tautological `(1,1)`-class `c = ∑ᵢ γᵢ ⊗ eᵢ`.  Its `p`-th power is
`(−1)^{p(p−1)/2} p!` times the tautological `(p,p)`-class `θ_p = ∑_{|I|=p} γ_I ⊗ e_I`. -/
noncomputable def taut (N : ℕ) : EA N := ∑ i : Fin N, ι ℚ (gam i) * ι ℚ (eb i)

/-- An explicit **non**-symmetric period matrix, for the sharpness half. -/
def badQ : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]


/-! ### The heart: a symmetric matrix contracted against an antisymmetric wedge -/

theorem col_eq {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) :
    ((0 : Fin N → ℚ), fun m => Q m i) = ∑ m : Fin N, Q m i • (eb m : W N) := by
  have h1 : (∑ m : Fin N, Q m i • (eb m : W N)).1 = (0 : Fin N → ℚ) := by
    simp [Prod.fst_sum, eb]
  have h2 : (∑ m : Fin N, Q m i • (eb m : W N)).2 = fun m => Q m i := by
    simp only [Prod.snd_sum, Prod.smul_snd, eb]
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  exact Prod.ext_iff.mpr ⟨h1.symm, h2.symm⟩

theorem iota_col {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) :
    ι ℚ ((0 : Fin N → ℚ), fun m => Q m i) = ∑ m : Fin N, Q m i • ι ℚ (eb m) := by
  rw [col_eq, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul]

theorem qmap_gam {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) :
    qmap Q (gam i) = (0, fun m => Q m i) := by
  ext m <;> simp [qmap, gam, Matrix.mulVec_single]

theorem qmap_eb {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) : qmap Q (eb i) = 0 := by
  simp [qmap, eb]

theorem swap_neg {N : ℕ} (x y : W N) : ι ℚ x * ι ℚ y = -(ι ℚ y * ι ℚ x) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

/-- `φ(c)` in coordinates: `∑ᵢ (i-th column of Q) ∧ eᵢ`.  The `Γ₂`-half of `c` is killed by
`φ`, so only the `γ`-half contributes, and it contributes its `Q`-column. -/
theorem phi_taut_expand {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) :
    phi Q (taut N) = ∑ i : Fin N, ι ℚ ((0 : Fin N → ℚ), fun m => Q m i) * ι ℚ (eb i) := by
  rw [taut, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phi_mul, phi_iota, phi_iota, qmap_eb, qmap_gam, map_zero, mul_zero, zero_add]

/-- **The heart of Lemma A.**  `φ(c) = ∑_{i,m} Q_{mi} · (e_m ∧ e_i)`, and that sum equals its
own negative because `Q` is symmetric while `e_m ∧ e_i` is antisymmetric; over `ℚ` this forces
it to vanish. -/
theorem phi_taut {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (hQ : ∀ i j, Q i j = Q j i) :
    phi Q (taut N) = 0 := by
  set v : Fin N → EA N := fun m => ι ℚ (eb m) with hv
  have h1 : phi Q (taut N) = ∑ i : Fin N, ∑ m : Fin N, Q m i • (v m * v i) := by
    rw [phi_taut_expand]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iota_col, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_mul_assoc]
  have key : (∑ i : Fin N, ∑ m : Fin N, Q m i • (v m * v i))
      = -∑ i : Fin N, ∑ m : Fin N, Q m i • (v m * v i) := by
    calc (∑ i : Fin N, ∑ m : Fin N, Q m i • (v m * v i))
        = ∑ m : Fin N, ∑ i : Fin N, Q m i • (v m * v i) := Finset.sum_comm
      _ = ∑ m : Fin N, ∑ i : Fin N, -(Q i m • (v i * v m)) := by
            refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
            rw [hQ m i, swap_neg, smul_neg]
      _ = -∑ m : Fin N, ∑ i : Fin N, Q i m • (v i * v m) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun m _ => Finset.sum_neg_distrib _
  have h2 : (2 : ℚ) • (∑ i : Fin N, ∑ m : Fin N, Q m i • (v m * v i)) = 0 := by
    rw [two_smul]; nth_rewrite 2 [key]; simp
  rw [h1]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **Lemma A.**  Leibniz then propagates the vanishing to every power. -/
theorem phi_pow {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℚ) (hQ : ∀ i j, Q i j = Q j i) (p : ℕ) :
    phi Q (taut N ^ p) = 0 := by
  induction p with
  | zero => rw [pow_zero]; exact phi_one Q
  | succ n ih => rw [pow_succ, phi_mul, ih, phi_taut Q hQ, mul_zero, zero_mul, add_zero]

/-! ### Sharpness: an explicit `4 × 4` model in which `φ(c) ≠ 0` for a non-symmetric `Q`

`M1` and `M2` are left multiplication by `f₁` and `f₂` on `⋀(ℚ²)`, written in the basis
`1, f₁, f₂, f₁f₂`.  They square to zero and anticommute, so `w ↦ w₂(0)·M1 + w₂(1)·M2` lifts to
an algebra map `⋀(Γ₁ ⊕ Γ₂) → M₄(ℚ)`, under which `e₁ ∧ e₂` goes to `M1 * M2 ≠ 0`. -/

def M1 : Matrix (Fin 4) (Fin 4) ℚ := !![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0]
def M2 : Matrix (Fin 4) (Fin 4) ℚ := !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,-1,0,0]

theorem hM11 : M1 * M1 = 0 := by
  ext i j
  have h4 : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  rcases h4 i with rfl|rfl|rfl|rfl <;> rcases h4 j with rfl|rfl|rfl|rfl <;>
    simp [M1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue]

theorem hM22 : M2 * M2 = 0 := by
  ext i j
  have h4 : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  rcases h4 i with rfl|rfl|rfl|rfl <;> rcases h4 j with rfl|rfl|rfl|rfl <;>
    simp [M2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue]

theorem hM12 : M1 * M2 + M2 * M1 = 0 := by
  ext i j
  have h4 : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  rcases h4 i with rfl|rfl|rfl|rfl <;> rcases h4 j with rfl|rfl|rfl|rfl <;>
    simp [M1, M2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue]

theorem hM12ne : M1 * M2 ≠ 0 := by
  intro h
  have h30 := congrFun (congrFun h 3) 0
  simp [M1, M2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val, Fin.isValue] at h30

noncomputable def rep : W 2 →ₗ[ℚ] Matrix (Fin 4) (Fin 4) ℚ where
  toFun w := w.2 0 • M1 + w.2 1 • M2
  map_add' x y := by simp [add_smul]; abel
  map_smul' r x := by simp [smul_add, smul_smul]

theorem rep_sq (w : W 2) : rep w * rep w = 0 := by
  simp only [rep, LinearMap.coe_mk, AddHom.coe_mk, add_mul, mul_add, smul_mul_assoc,
             mul_smul_comm, smul_smul, hM11, hM22, smul_zero, zero_add, add_zero]
  rw [mul_comm (w.2 1) (w.2 0), ← smul_add, add_comm (M2 * M1) (M1 * M2), hM12, smul_zero]

noncomputable def repHom : EA 2 →ₐ[ℚ] Matrix (Fin 4) (Fin 4) ℚ :=
  ExteriorAlgebra.lift ℚ ⟨rep, rep_sq⟩

theorem repHom_iota (w : W 2) : repHom (ι ℚ w) = rep w := by simp [repHom]

theorem eb_prod_ne : ι ℚ (eb (0 : Fin 2)) * ι ℚ (eb 1) ≠ 0 := by
  intro h
  have h2 := congrArg repHom h
  rw [map_mul, map_zero, repHom_iota, repHom_iota] at h2
  have e0 : rep (eb (0 : Fin 2)) = M1 := by simp [rep, eb, Pi.single_apply]
  have e1 : rep (eb (1 : Fin 2)) = M2 := by simp [rep, eb, Pi.single_apply]
  rw [e0, e1] at h2
  exact hM12ne h2

/-- **Sharpness.**  For the non-symmetric `Q = ![![0,1],![0,0]]` the first column vanishes and
the second is `e₁`, so `φ(c) = e₁ ∧ e₂ ≠ 0`. -/
theorem phi_badQ_ne : phi badQ (taut 2) ≠ 0 := by
  have hc0 : ((0 : Fin 2 → ℚ), fun m => badQ m 0) = (0 : W 2) := by
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    funext m
    have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases h2 m with rfl|rfl <;> simp [badQ, Matrix.cons_val, Fin.isValue]
  have hc1 : ((0 : Fin 2 → ℚ), fun m => badQ m 1) = (eb (0 : Fin 2)) := by
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    funext m
    have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases h2 m with rfl|rfl <;>
      simp [badQ, eb, Pi.single_apply, Matrix.cons_val, Fin.isValue]
  rw [phi_taut_expand, Fin.sum_univ_two, hc0, hc1, map_zero, zero_mul, zero_add]
  exact eb_prod_ne

/-- **Lemma A, with its sharpness.**  The eigenwave annihilates every power of the tautological
class exactly when the period matrix is symmetric, i.e. exactly when it is a polarisation. -/
theorem proof :
    (∀ (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℚ), (∀ i j, Q i j = Q j i) →
        ∀ p : ℕ, phi Q (taut N ^ p) = 0)
    ∧ phi badQ (taut 2) ≠ 0 :=
  ⟨fun N Q hQ p => phi_pow Q hQ p, phi_badQ_ne⟩

end Submissions.EigenwaveKernelPolarisation.LemmaA
