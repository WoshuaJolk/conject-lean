import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin

/-!
# EigenwaveKernelPolarisation — the tautological class is a tropical Hodge class iff `Q` is symmetric

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What is proved

Let `Γ₁` and `Γ₂` be the two lattices of a maximally degenerate tropical abelian variety
`X = (Γ₂ ⊗ ℝ)/Γ₁` of dimension `N`, with `Γ₁ ⊂ Γ₂ ⊗ ℝ` the period lattice cut out by a
polarisation matrix `Q`: Zharkov, arXiv:2002.02347, *"The columns of the matrix `Q` can be
thought of as the coordinates of a basis for the other (period) lattice
`Γ₁ ⊂ Γ₂ ⊗ ℝ`."*  Write `φ` for the **eigenwave / tropical monodromy operator** of
Mikhalkin–Zharkov (arXiv:1302.0252, *Tropical eigenwave and intermediate Jacobians*; the
title is misprinted as *"Tropical waves and intermediate Jacobians"* in the bibliography of
arXiv:2002.02347).  On a totally degenerate abelian variety, cap product with the eigenwave
class is

  `φ(γ_{i₁} ∧ ⋯ ∧ γ_{i_p} ⊗ β) = ∑ₖ (−1)^{k−1} (γ_{i₁} ∧ ⋯ γ̂_{i_k} ⋯ ∧ γ_{i_p}) ⊗ (Q_{·,i_k} ∧ β)`

with `Q_{·,i}` the `i`-th column of `Q` read in the `e`-basis of `Γ₂`.  Amini–Piquerez
(arXiv:2012.13142, Thm 5.2) identify this operator with the tropical monodromy operator `N`,
and conjecture (Conj. 1.2, the *tropical Hodge conjecture*) that its kernel in `H^{p,p}` is
exactly the span of the classes of codimension-`p` tropical cycles.  So `ker φ` is where a
tropical Hodge class has to live, and this statement locates the tautological class in it.

**Theorem (Lemma A).**  Let `c := ∑ᵢ γᵢ ⊗ eᵢ` be the tautological `(1,1)`-class.  If `Q` is
symmetric — i.e. exactly when `Q` is a polarisation, rather than an arbitrary period matrix —
then `φ(cᵖ) = 0` for every `p`.

**Sharpness.**  For the non-symmetric `Q = ![![0,1],![0,0]]` at `N = 2`, `φ(c) ≠ 0`.  So the
hypothesis is not decoration and the theorem is not vacuous: `c ∈ ker φ` is *equivalent* to
`Q` being symmetric.  The proof of sharpness exhibits an explicit `4 × 4` faithful-enough
representation of the relevant piece of the exterior algebra, so the non-vanishing is a
computation, not an appeal to a dimension count.

The mathematical content is one line: `φ(c) = ∑_{i,m} Q_{mi} · (e_m ∧ e_i)`, and a symmetric
matrix contracted against an antisymmetric wedge is zero.  Everything else is Leibniz.

## How `φ` is realised, and the one convention that differs

`Γ₁ ⊕ (Γ₂ ⊗ ℚ)` is `W N = (Fin N → ℚ) × (Fin N → ℚ)` and the ambient algebra is
`EA N = ⋀(Γ₁ ⊕ Γ₂ ⊗ ℚ)`.  The graded piece `⋀^q Γ₁ ⊗ ⋀^r Γ₂` sits inside `EA N` as the span
of products `γ_{i₁} ⋯ γ_{i_q} · e_{j₁} ⋯ e_{j_r}`, and this embedding is injective, so working
in the single algebra `EA N` loses nothing.  `γᵢ` is `gam i`, `eᵢ` is `eb i`.

`φ` is then the **even derivation of `EA N` extending the linear map `qmap Q`**, which sends
`γ ↦ Qγ ∈ Γ₂` and kills `Γ₂`.  It is constructed by lifting `w ↦ (ι w, ι (Q̃ w))` through the
universal property of the exterior algebra into the square-zero extension
`TrivSqZeroExt (EA N) (EA N)`: the lift exists because `ι x · ι y + ι y · ι x = 0`, so the
image of every `w` squares to zero.  `phi_mul` (Leibniz), `phi_iota` (`φ(ι w) = ι (Q̃ w)`) and
`phi_one` are proved below, and they characterise `φ` completely.

**The convention.**  Deleting `γ_{i_k}` *in place* and then moving `Q_{·,i_k}` to the right of
the surviving `γ`'s costs `(−1)^{p−k}`, whereas the displayed formula above carries
`(−1)^{k−1}`.  The two therefore differ by the global sign `(−1)^{p+1}` on the summand of
`Γ₁`-degree `p`.  A global nonzero scalar on a homogeneous summand does not move the kernel,
which is the only thing claimed here, and `c ^ p` is `Γ₁`-homogeneous of degree `p`.

## `c ^ p` versus `θ_p = ∑_{|I| = p} γ_I ⊗ e_I`

`c ^ p = (−1)^{p(p−1)/2} · p! · θ_p`, where `θ_p := ∑_{|I| = p} γ_I ⊗ e_I` is the tautological
`(p,p)`-class in the index-set presentation (at `p = 2`, `N = 4` this is Zharkov's `θ`, the
class the rest of this problem is about).  The reason is elementary: expanding the `p`-th power
of `c = ∑ᵢ γᵢ eᵢ`, the terms with a repeated index die because `γᵢ γᵢ = 0`, each of the `p!`
orderings of a fixed `I` gives the same term (the `γ`-side and the `e`-side pick up the same
sign, so the two signs cancel), and moving every `e` to the right of every `γ` costs
`(−1)^{p(p−1)/2}` uniformly in `I`.

**This scalar identity is NOT formalised here.**  It is checked symbolically in sympy for the
cases used (`eigenwave_phi.py`, `proof_phi_kernel.py`), and it is a standard fact — `θ_p` is
the `p`-th divided power of `c`.  Since `p!` and the sign are invertible in `ℚ`, the theorem
proved here is equivalent to `φ(θ_p) = 0`; but a reader who wants `θ_p` written as a sum over
`p`-element subsets should treat that translation as an unformalised step, and the statement
below is deliberately phrased in terms of `c ^ p` rather than pretending otherwise.

## What is claimed, and what is not

**Claimed.**  `φ(c ^ p) = 0` for every `N`, every symmetric rational `Q` and every `p`; and
`φ(c) ≠ 0` for an explicit non-symmetric `Q`.

**Not claimed.**

* That `φ` as constructed here is *the* eigenwave up to nothing at all — the global sign
  `(−1)^{p+1}` per `Γ₁`-degree is a convention difference, recorded above.
* The identity `c ^ p = (−1)^{p(p−1)/2} p! θ_p` (see the previous section).
* Anything about the Weil classes.  `φ(W₁) = φ(W₂) = 0` for a Weil-type polarisation is a
  separate statement with a separate proof (Lemma B: `Q` intertwines the two `CM` actions, so
  it carries the `+δ` eigenspace `A ⊂ Γ₁ ⊗ K` into the `+δ` eigenspace `B ⊂ Γ₂ ⊗ K`, and every
  term of `φ(ω⁺)` then contains an `(n+1)`-fold wedge inside the `n`-dimensional `B`).
* That membership of `ker φ` implies a class is algebraic.  That is Amini–Piquerez's
  Conjecture 1.2, and it is open.  `ker φ` is a *necessary* condition for a tropical Hodge
  class, which is why a positive answer here is a prerequisite and not a conclusion.
* Anything about complex abelian varieties or the classical Hodge conjecture.
-/

namespace Statements.EigenwaveKernelPolarisation

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

/-- The canonical proposition.  This is the type the verifier demands.

**Lemma A and its sharpness.**  For every rank `N`, every *symmetric* rational `Q` — that is,
exactly when `Q` is a polarisation — the eigenwave `φ` annihilates every power of the
tautological class `c = ∑ᵢ γᵢ ⊗ eᵢ`; and for the explicit non-symmetric `Q = ![![0,1],![0,0]]`
it does not annihilate `c`. -/
abbrev statement : Prop :=
  (∀ (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℚ), (∀ i j, Q i j = Q j i) →
      ∀ p : ℕ, phi Q (taut N ^ p) = 0)
  ∧ phi badQ (taut 2) ≠ 0

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.EigenwaveKernelPolarisation
