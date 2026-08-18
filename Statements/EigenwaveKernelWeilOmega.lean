import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# EigenwaveKernelWeilOmega — the Weil class of a tropical abelian `2n`-fold is a tropical Hodge class

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The claim

Let `X` be a maximally degenerate tropical abelian `2n`-fold of Weil type, with lattices `Γ₁`
and `Γ₂` of rank `2n` and polarisation matrix `Q`; let `K` carry `δ` with `δ² = −d`, and let

  `ω⁺ = (a₁ ∧ ⋯ ∧ a_n) ⊗ (b₁ ∧ ⋯ ∧ b_n) = W₁ + δ · W₂`

where `a_i = δ γ_i + γ_{n+i}` span the `+δ` eigenspace of the `CM` action on `Γ₁ ⊗ K` and
`b_i = e_i − δ e_{n+i}` span the `+δ` eigenspace on `Γ₂ ⊗ K`.  `W₁` and `W₂` are the two Weil
classes.  Then the eigenwave (= tropical monodromy) operator `φ` kills `ω⁺`.

**Why.**  Weil type says `Q` intertwines the two `CM` actions, `J₂ Q = Q J₁`; hence `Q` carries
the `+δ` eigenspace `A = span_K{a_i}` into the `+δ` eigenspace `B = span_K{b_i}`.  Every term
of `φ(ω⁺)` is obtained by deleting one `a_k` and inserting `Q a_k` next to `b₁ ∧ ⋯ ∧ b_n`;
since `Q a_k` lies in the `n`-dimensional `B`, that term contains an `(n+1)`-fold wedge inside
an `n`-dimensional space and vanishes.

This closes, for every `n`, the gap flagged for the dimension-8 programme: the two Weil classes
of a maximally degenerate abelian `2n`-fold of split Weil type are tropical Hodge classes in the
sense of Amini–Piquerez (arXiv:2012.13142, Conj. 1.2), whose kernel-of-monodromy criterion is
what "tropical Hodge class" means.  Dimension 8 is the first case that Markman's theorem
(arXiv:2502.03415, which settles **all** abelian fourfolds of Weil type, **all** discriminants)
does not already cover; so this is the object the tropical route needs, and it is what it is
claimed to be.

## What the statement contains

Three conjuncts.

1. **The lemma, abstractly.**  For any commutative ring `K`, any index type `T`, any matrix `Q`,
   and any `a₁,…,a_n ∈ Γ₁ ⊗ K`, `b₁,…,b_n ∈ Γ₂ ⊗ K`: if `Q a_k ∈ span_K{b₁,…,b_n}` for every
   `k`, then `φ(ω⁺) = 0`.  This is the whole proof, and `Q A ⊆ B` is exactly the Weil-type
   hypothesis in the form in which it is used.

2. **The Weil-type family satisfies that hypothesis, in every dimension.**  With
   `Q = [[P, R], [−R, dP]]` (the general-`n` Weil-type polarisation; at `n = 2` this is
   Zharkov's matrix, arXiv:2002.02347), `J₁ = [[0, −dI], [I, 0]]`, `J₂ = [[0, −I], [dI, 0]]`:
   `J₂ Q = Q J₁`; the `a_k` are `+δ` eigenvectors of `J₁`; the `b_i` are `+δ` eigenvectors of
   `J₂`; and

     `Q a_k = ∑ᵢ (R_{ik} + δ P_{ik}) b_i`,

   which is the explicit form of `Q(A) ⊆ B`.  Note that no symmetry of `P` and no antisymmetry
   of `R` is needed for this: only `δ² = −d` and the block shape.

3. **The conclusion for the Weil family**: `φ(ω⁺) = 0` for that `Q`, every `n`, every `P`, `R`,
   every `d` and every `δ` with `δ² = −d`.

## How `φ` is realised

Exactly as in `EigenwaveKernelPolarisation` (p/8?s=7), but over a general commutative ring `K`
and a general index type `T`.  `Γ₁ ⊗ K ⊕ Γ₂ ⊗ K` is `Wd K T = (T → K) × (T → K)`, the ambient
algebra is `⋀(Γ₁ ⊕ Γ₂)`, in which `⋀^q Γ₁ ⊗ ⋀^r Γ₂` sits as the span of the products
`γ_{i₁} ⋯ γ_{i_q} e_{j₁} ⋯ e_{j_r}`, and `φ` is the even derivation extending `γ ↦ Qγ ∈ Γ₂`,
`e ↦ 0`.  It is built by lifting `w ↦ (ι w, ι (Q̃ w))` into the square-zero extension through
the universal property, the lift existing because `ι x · ι y + ι y · ι x = 0`.  `phi_mul`
(Leibniz), `phi_iota` and `phi_one` are proved below and characterise `φ`.  As there, this `φ`
differs from Mikhalkin–Zharkov's displayed formula (arXiv:1302.0252) by the global sign
`(−1)^{p+1}` on the summand of `Γ₁`-degree `p`, which does not move the kernel.

`ω⁺` is `omegaPlus`, the product of the ordered wedge of the `a`'s (in the `Γ₁` half) with the
ordered wedge of the `b`'s (in the `Γ₂` half).

## What is claimed, and what is not

**Claimed.**  The three conjuncts above, for every `n` and every commutative ring `K` with an
element `δ` satisfying `δ² = −d`.

**Not claimed.**

* **The splitting `ω⁺ = W₁ + δ W₂` is not formalised.**  What is proved is `φ(ω⁺) = 0`.  To
  conclude `φ(W₁) = φ(W₂) = 0` separately one needs `K` free over the base with basis `{1, δ}`
  and `φ` to be defined over the base — both true in the intended application `K = ℚ(δ)`, `Q`
  rational, and both checked symbolically for `n = 2,3,4,5` (`check_phi_general_n.py`), but
  neither is a theorem here.
* **That `ker φ` implies algebraicity.**  That is Amini–Piquerez's Conjecture 1.2 and it is
  open.  Membership of `ker φ` is a *necessary* condition for a tropical Hodge class; a
  positive answer here is a prerequisite for the programme, not a conclusion of it.
* Anything about Kontsevich's `Φ`-system, about tropical algebraic cycles representing these
  classes, or about complex abelian varieties and the classical Hodge conjecture.
* That the block form `[[P, R], [−R, dP]]` is the *only* general-`n` Weil-type polarisation.
  It is the one that specialises to Zharkov's at `n = 2` and has the right parameter count
  `n²`; that identification is argued elsewhere and is not a theorem here.
-/

namespace Statements.EigenwaveKernelWeilOmega

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

/-- The canonical proposition.  This is the type the verifier demands.

**Lemma B.**  (1) If `Q` carries every `a_k` into the span of the `b_i`, then the eigenwave
kills `ω⁺ = (a₁ ∧ ⋯ ∧ a_n) ⊗ (b₁ ∧ ⋯ ∧ b_n)`.  (2) The general-`n` Weil-type polarisation does
carry `A` into `B`: it intertwines the two `CM` actions, the `a_k` and `b_i` really are the
`+δ` eigenvectors, and `Q a_k = ∑ᵢ (R_{ik} + δ P_{ik}) b_i`.  (3) Hence the eigenwave kills the
Weil `ω⁺` in every dimension. -/
abbrev statement : Prop :=
  (∀ (K : Type) [CommRing K] (T : Type) [Fintype T] (Q : Matrix T T K) (n : ℕ)
      (av bv : Fin n → (T → K)),
      (∀ k, ∃ c : Fin n → K, Q.mulVec (av k) = ∑ i, c i • bv i) →
      phi Q (omegaPlus av bv) = 0)
  ∧ (∀ (K : Type) [CommRing K] (n : ℕ) (d δ : K) (P R : Matrix (Fin n) (Fin n) K),
      δ * δ = -d →
        (J2 d * Qweil d P R = Qweil d P R * J1 d)
      ∧ (∀ k : Fin n, (J1 (n := n) d).mulVec (aWeil δ k) = δ • aWeil (n := n) δ k)
      ∧ (∀ i : Fin n, (J2 (n := n) d).mulVec (bWeil δ i) = δ • bWeil (n := n) δ i)
      ∧ (∀ k, (Qweil d P R).mulVec (aWeil δ k)
                = ∑ i, (R i k + δ * P i k) • bWeil δ i))
  ∧ (∀ (K : Type) [CommRing K] (n : ℕ) (d δ : K) (P R : Matrix (Fin n) (Fin n) K),
      δ * δ = -d → phi (Qweil d P R) (omegaPlus (aWeil δ) (bWeil δ)) = 0)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.EigenwaveKernelWeilOmega
