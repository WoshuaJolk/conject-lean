import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-!
# WeilDegenerationSplit — a maximally degenerate Weil fourfold is of split Weil type

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The informal statement

Let `A` be an abelian fourfold of Weil type for `K = ℚ(√-d)`, with polarisation form `E` on
`H₁(A,ℚ)` and `f` the action of `√-d`.  Van Geemen (*An introduction to the Hodge conjecture
for abelian varieties*, LNM 1594, Lemma 5.2) attaches the `K`-hermitian form

  `H(x,y) = E(x, f y) + √-d · E(x,y)`

on `H₁(A,ℚ)` as a `K`-vector space; `det H ∈ ℚ*/Nm(K*)` — the **discriminant** — is an
isogeny invariant, and by Deligne–Milne (LNM 900, Cor. 4.2) it equals `(-1)ⁿ` exactly when
`(A,K,E)` is of **split** Weil type.

Kontsevich's tropical programme (Zharkov, arXiv:2002.02347) works with a **maximally
degenerate** abelian fourfold: `H₁ = Γ₁ ⊕ Γ₂` with `Γ₂` the lattice of vanishing cycles,
`Γ₁ ≅ Γ₂*` via the principal polarisation, both summands `E`-isotropic, and the `√-d` action
preserving each — exactly Zharkov's data, `(e₁,e₂,e₃,e₄) ↦ (d e₃, d e₄, -e₁, -e₂)` and
`(γ₁,γ₂,γ₃,γ₄) ↦ (γ₃,γ₄,-d γ₁,-d γ₂)`.

The point recorded here is that `Γ₂ ⊗ ℚ` is then an `f`-stable, `E`-isotropic `K`-subspace of
half the `K`-dimension, so **both** components of `H` vanish identically on it: `H` is
hyperbolic, the fourfold is of split Weil type, and the discriminant is `1` — for every value
of Zharkov's parameters `a, b, c, e`, since neither `E` nor `f` involves them.  A tropical
degeneration therefore cannot reach a Weil fourfold of non-split discriminant.

Stated below as identities about explicit `8 × 8` integer matrices, so the kernel decides
them.  The step from "`H` vanishes on an `f`-stable isotropic half" to "`det H = (-1)ⁿ`" is
classical hermitian form theory and is **not** claimed here; what is claimed is its input.

**Attribution.**  P. Brosnan announced an observation with the same consequence in dimension
four (IBS Center for Complex Geometry, 20–21 July 2023, "How Markman Saves the Hodge
Conjecture (for Weil Type Abelian Fourfolds) from Kontsevich"); it appears never to have been
written up.  The matrices and identities below are an independent derivation.

## Read-back, term by term

* `H₁ = Γ₁ ⊕ Γ₂` → `Fin 8`: `0,1,2,3` are `γ₁ … γ₄`, and `4,5,6,7` are `e₁ … e₄`.
* the principal polarisation → `Emat`, with `E(γᵢ, eⱼ) = δᵢⱼ`, `E(eⱼ, γᵢ) = -δᵢⱼ`, zero on
  `Γ₁ × Γ₁` and on `Γ₂ × Γ₂`.
* the `√-d` action → `Fmat d`; entry `(i,j)` is the `i`-th coordinate of the image of the
  `j`-th basis vector.
* "`f² = -d`" → `mul (Fmat d) (Fmat d) i j = if i = j then -d else 0`.
* "`E` is a Weil-type polarisation for `f`" → `Eᵀ = -E` and `Fᵀ E F = d · E`.
* "`E` is nondegenerate" → `mul Emat Emat = -1`, which forces invertibility.
* "`Γ₂` is `E`-isotropic and `f`-stable" → the vanishing statements on indices `≥ 4`.
* "`H` vanishes on `Γ₂`" → both `E(x,y) = 0` and `E(x, f y) = 0` there, the latter being the
  matrix `E · F`.
-/

namespace Statements.WeilDegenerationSplit

/-- Basis index for `H₁ = Γ₁ ⊕ Γ₂`: `0,1,2,3` are `γ₁ … γ₄`; `4,5,6,7` are `e₁ … e₄`. -/
abbrev Idx : Type := Fin 8

/-- The principal polarisation `E`: `E(γᵢ, eⱼ) = δᵢⱼ`, `E(eⱼ, γᵢ) = -δᵢⱼ`, with `Γ₁` and `Γ₂`
both isotropic. -/
def Emat : Idx → Idx → ℤ
  | 0, 4 => 1 | 1, 5 => 1 | 2, 6 => 1 | 3, 7 => 1
  | 4, 0 => -1 | 5, 1 => -1 | 6, 2 => -1 | 7, 3 => -1
  | _, _ => 0

/-- The action of `√-d`, in Zharkov's normalisation. -/
def Fmat (d : ℤ) : Idx → Idx → ℤ
  | 2, 0 => 1 | 3, 1 => 1 | 0, 2 => -d | 1, 3 => -d
  | 6, 4 => d | 7, 5 => d | 4, 6 => -1 | 5, 7 => -1
  | _, _ => 0

/-- Matrix product. -/
def mul (A B : Idx → Idx → ℤ) : Idx → Idx → ℤ := fun i j => ∑ k : Idx, A i k * B k j

/-- Transpose. -/
def tr (A : Idx → Idx → ℤ) : Idx → Idx → ℤ := fun i j => A j i

/-- The canonical proposition.  This is the type the verifier demands.

For every `d`: `E` is alternating and nondegenerate, `f² = -d`, `f` is a similitude of `E`
with factor `d` — so `(E,f)` really is Weil-type data — the vanishing-cycle half `Γ₂` is
`E`-isotropic and `f`-stable, and consequently **both** components of van Geemen's hermitian
form vanish identically on `Γ₂`. -/
abbrev statement : Prop :=
  ∀ d : ℤ,
    (∀ i j : Idx, Emat i j = -Emat j i)
  ∧ (∀ i j : Idx, mul Emat Emat i j = if i = j then -1 else 0)
  ∧ (∀ i j : Idx, mul (Fmat d) (Fmat d) i j = if i = j then -d else 0)
  ∧ (∀ i j : Idx, mul (tr (Fmat d)) (mul Emat (Fmat d)) i j = d * Emat i j)
  ∧ (∀ i j : Idx, 4 ≤ (i : ℕ) → 4 ≤ (j : ℕ) → Emat i j = 0)
  ∧ (∀ i j : Idx, 4 ≤ (j : ℕ) → (i : ℕ) < 4 → Fmat d i j = 0)
  ∧ (∀ i j : Idx, 4 ≤ (i : ℕ) → 4 ≤ (j : ℕ) → mul Emat (Fmat d) i j = 0)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.WeilDegenerationSplit
