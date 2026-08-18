import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Deliberately weakened control for `EigenwaveKernelPolarisation` — expected RED

This is an honesty gate, not a claim.  Both halves of the canonical proposition are gutted.

* The universal quantifier over the exponent `p` is cut to the single case `p = 0`, where the
  claim degenerates to `φ(c⁰) = φ(1) = 0` — true of any derivation, and in particular true
  without the symmetry of `Q`, which is never used.  Nothing at all is said about `c`, let
  alone about its higher powers.
* The sharpness clause `φ_badQ(c) ≠ 0` is replaced by the tautology
  `φ_badQ(c) = φ_badQ(c)`.  The `4 × 4` representation and the non-vanishing argument are gone,
  so the weakened proposition is compatible with `φ` being identically zero.

The proposition is therefore strictly weaker than
`Statements.EigenwaveKernelPolarisation.statement`, and the verifier's bridge check
`example : Statements.EigenwaveKernelPolarisation.statement := proof` must fail.  Submitted
with `expect: "red"`, `expect_reason: "restatement"`.  If this greens, the bridge is not
checking what it claims to check and the companion green artifact should not be trusted
either.
-/

namespace Submissions.EigenwaveKernelPolarisation.Weak

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


/-- The weakened proposition: `p = 0` only, and the sharpness clause replaced by a tautology. -/
theorem proof :
    (∀ (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℚ), (∀ i j, Q i j = Q j i) →
        phi Q (taut N ^ 0) = 0)
    ∧ phi badQ (taut 2) = phi badQ (taut 2) := by
  refine ⟨?_, rfl⟩
  intro N Q _hQ
  rw [pow_zero]
  exact phi_one Q

end Submissions.EigenwaveKernelPolarisation.Weak
