import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# Deliberately weakened control for `EigenwaveKernelWeilOmega` — expected RED

This is an honesty gate, not a claim.  All three conjuncts are gutted.

* Conjunct 1, the abstract lemma, is restricted to `n = 0`.  There `ω⁺` is the empty product
  `1` and the claim is `φ(1) = 0`, true of any derivation; the hypothesis `Q a_k ∈ span{b_i}`
  is vacuous because there are no `k`.  The `(n+1)`-fold wedge argument — the entire content —
  never appears.
* Conjunct 2 keeps only `J₂ Q = Q J₁`, the one clause that holds by block multiplication alone
  and never uses `δ² = −d`.  The two eigenvector clauses and the operative identity
  `Q a_k = ∑ᵢ (R_{ik} + δ P_{ik}) b_i` — the actual bridge to Weil type — are dropped.
* Conjunct 3, the conclusion for the Weil family, is likewise cut to `n = 0`.

The proposition is therefore strictly weaker than
`Statements.EigenwaveKernelWeilOmega.statement`, and the verifier's bridge check
`example : Statements.EigenwaveKernelWeilOmega.statement := proof` must fail.  Submitted with
`expect: "red"`, `expect_reason: "restatement"`.  If this greens, the bridge is not checking
what it claims to check and the companion green artifact should not be trusted either.
-/

namespace Submissions.EigenwaveKernelWeilOmega.Weak

open ExteriorAlgebra

open ExteriorAlgebra

/-- `Γ₁ ⊗ K ⊕ Γ₂ ⊗ K`, both halves indexed by `T`. -/
abbrev Wd (K : Type) [CommRing K] (T : Type) : Type := (T → K) × (T → K)

/-- `⋀(Γ₁ ⊕ Γ₂)`, inside which `⋀^q Γ₁ ⊗ ⋀^r Γ₂` is the span of the products
`γ_{i₁} ⋯ γ_{i_q} e_{j₁} ⋯ e_{j_r}`. -/
abbrev EAd (K : Type) [CommRing K] (T : Type) : Type := ExteriorAlgebra K (Wd K T)

/-- The square-zero extension used to build `φ` as a derivation. -/
abbrev TSd (K : Type) [CommRing K] (T : Type) : Type :=
  TrivSqZeroExt (EAd K T) (EAd K T)

variable {K : Type} [CommRing K] {T : Type} [Fintype T]

/-- `Q̃ : γ ↦ Qγ ∈ Γ₂`, `e ↦ 0`. -/
noncomputable def qmap (Q : Matrix T T K) : Wd K T →ₗ[K] Wd K T :=
  (LinearMap.inr K _ _).comp ((Matrix.mulVecLin Q).comp (LinearMap.fst K _ _))

/-- `w ↦ ι w + ε · ι (Q̃ w)`. -/
noncomputable def Fmap (Q : Matrix T T K) : Wd K T →ₗ[K] TSd K T where
  toFun w := TrivSqZeroExt.inl (ι K w) + TrivSqZeroExt.inr (ι K (qmap Q w))
  map_add' x y := by simp [map_add]; abel
  map_smul' r x := by simp [map_smul]

theorem Fmap_sq (Q : Matrix T T K) (w : Wd K T) : Fmap Q w * Fmap Q w = 0 := by
  apply TrivSqZeroExt.ext
  · simp [Fmap, TrivSqZeroExt.fst_mul]
  · simp [Fmap, TrivSqZeroExt.snd_mul, ExteriorAlgebra.ι_add_mul_swap]

noncomputable def Lift (Q : Matrix T T K) : EAd K T →ₐ[K] TSd K T :=
  ExteriorAlgebra.lift K ⟨Fmap Q, Fmap_sq Q⟩

/-- **The eigenwave operator** `φ`: the even derivation of `⋀(Γ₁ ⊕ Γ₂)` extending `γ ↦ Qγ`,
`e ↦ 0`. -/
noncomputable def phi (Q : Matrix T T K) : EAd K T →+ EAd K T where
  toFun x := (Lift Q x).snd
  map_zero' := by simp
  map_add' x y := by simp [map_add]

theorem lift_fst (Q : Matrix T T K) (x : EAd K T) : (Lift Q x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K (EAd K T) (EAd K T)).comp (Lift Q)
      = AlgHom.id K (EAd K T) := by
    apply ExteriorAlgebra.hom_ext; apply LinearMap.ext; intro w; simp [Lift, Fmap]
  exact congrArg (fun f => f x)
    (congrArg (fun (f : EAd K T →ₐ[K] EAd K T) => (f : EAd K T → EAd K T)) h)

theorem phi_iota (Q : Matrix T T K) (w : Wd K T) : phi Q (ι K w) = ι K (qmap Q w) := by
  simp [phi, Lift, Fmap]

/-- **Leibniz.** -/
theorem phi_mul (Q : Matrix T T K) (x y : EAd K T) :
    phi Q (x * y) = x * phi Q y + phi Q x * y := by
  simp [phi, map_mul, TrivSqZeroExt.snd_mul, lift_fst]

theorem phi_one (Q : Matrix T T K) : phi Q (1 : EAd K T) = 0 := by simp [phi]

/-- A vector of `Γ₁ ⊗ K`. -/
def gamv (v : T → K) : Wd K T := (v, 0)

/-- A vector of `Γ₂ ⊗ K`. -/
def ebv (v : T → K) : Wd K T := (0, v)

/-- `ω⁺ = (a₁ ∧ ⋯ ∧ a_n) ⊗ (b₁ ∧ ⋯ ∧ b_n)`, the `a`'s in `Γ₁` and the `b`'s in `Γ₂`. -/
noncomputable def omegaPlus {n : ℕ} (av bv : Fin n → (T → K)) : EAd K T :=
  (List.ofFn fun k => ι K (gamv (av k))).prod * (List.ofFn fun i => ι K (ebv (bv i))).prod

/-- The general-`n` Weil-type polarisation `Q = [[P, R], [−R, dP]]`.  At `n = 2`, with `P`
symmetric and `R` antisymmetric, this is Zharkov's matrix. -/
def Qweil {n : ℕ} (d : K) (P R : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks P R (-R) (d • P)

/-- `√−d` acting on `Γ₁`: `γ_i ↦ γ_{n+i}`, `γ_{n+i} ↦ −d γ_i`. -/
def J1 {n : ℕ} (d : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 (-(d • (1 : Matrix (Fin n) (Fin n) K))) 1 0

/-- `√−d` acting on `Γ₂`: `e_i ↦ d e_{n+i}`, `e_{n+i} ↦ −e_i`. -/
def J2 {n : ℕ} (d : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 (-(1 : Matrix (Fin n) (Fin n) K)) (d • 1) 0

/-- `a_k = δ γ_k + γ_{n+k}`, a basis of the `+δ` eigenspace `A ⊂ Γ₁ ⊗ K`. -/
def aWeil {n : ℕ} (δ : K) (k : Fin n) : (Fin n ⊕ Fin n) → K :=
  Sum.elim (δ • Pi.single k 1) (Pi.single k 1)

/-- `b_i = e_i − δ e_{n+i}`, a basis of the `+δ` eigenspace `B ⊂ Γ₂ ⊗ K`. -/
def bWeil {n : ℕ} (δ : K) (i : Fin n) : (Fin n ⊕ Fin n) → K :=
  Sum.elim (Pi.single i 1) ((-δ) • Pi.single i 1)


/-- The weakened proposition: `n = 0` in the two wedge clauses, and only the `δ`-free half of
the Weil-type clause. -/
theorem proof :
    (∀ (K : Type) [CommRing K] (T : Type) [Fintype T] (Q : Matrix T T K)
        (av bv : Fin 0 → (T → K)),
        (∀ k, ∃ c : Fin 0 → K, Q.mulVec (av k) = ∑ i, c i • bv i) →
        phi Q (omegaPlus av bv) = 0)
    ∧ (∀ (K : Type) [CommRing K] (n : ℕ) (d δ : K) (P R : Matrix (Fin n) (Fin n) K),
        δ * δ = -d → J2 d * Qweil d P R = Qweil d P R * J1 d)
    ∧ (∀ (K : Type) [CommRing K] (d δ : K) (P R : Matrix (Fin 0) (Fin 0) K),
        δ * δ = -d → phi (Qweil d P R) (omegaPlus (aWeil δ) (bWeil δ)) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ T _ Q av bv _h
    simpa [omegaPlus] using phi_one Q
  · intro K _ n d δ P R _hd
    simp only [J1, J2, Qweil, Matrix.fromBlocks_multiply]
    congr 1 <;> simp
  · intro K _ d δ P R _hd
    simpa [omegaPlus] using phi_one (Qweil d P R)

end Submissions.EigenwaveKernelWeilOmega.Weak
