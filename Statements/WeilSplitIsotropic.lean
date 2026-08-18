import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Basic
/-!
# WeilSplitIsotropic — an `f`-stable isotropic half kills van Geemen's hermitian form, in every dimension

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What is claimed

Two things, in one proposition.

**Part A, the dimension-free lemma.**  Let `R` be a commutative ring, `V` an `R`-module,
`E : V × V → R` an alternating bilinear form, `f : V → V` an `R`-linear map with `f ∘ f = -d`
and `E (f x) (f y) = d * E x y`, and let `W ⊆ V` be a submodule that is `f`-stable and
`E`-isotropic.  Then **both** components of van Geemen's hermitian form

  `H(x,y) = E(x, f y) + √-d · E(x,y)`

vanish identically on `W`: `E x y = 0` *and* `E x (f y) = 0` for all `x, y ∈ W`.

The proof is one line — `f y ∈ W` because `W` is `f`-stable, and `W` is isotropic, so
`E x (f y) = 0` — and the hypotheses `E x x = 0`, `f (f x) = -(d • x)` and
`E (f x) (f y) = d * E x y` are carried but never used.  They are carried on purpose: they are
exactly the conditions that make `(V, E, f)` Weil-type data in van Geemen's sense (LNM 1594,
Lemma 5.2), so the reader can see that the conclusion is a statement about that situation and
not about an arbitrary pair of maps.  The value of Part A is coverage, not difficulty: it is
independent of `rank V`, of `d`, and of the field of definition.

**Part B, the bridge to Zharkov's family in every dimension.**  Part A on its own could be
about nothing.  Part B exhibits the maximally degenerate abelian `2n`-fold of Weil type,
for **every** `n`, as an instance of Part A's hypotheses, and computes the conclusion
directly.

## Why this is the barrier

Van Geemen (LNM 1594, Lemma 5.2(3)) shows `det H ∈ ℚ*/Nm(K*)` — the **discriminant** — is an
isogeny invariant of a polarised abelian variety of Weil type `(X, K, E)`; by Deligne–Milne
(LNM 900, Cor. 4.2) `(X, K, E)` is of **split** Weil type exactly when the discriminant is
`(-1)ⁿ`.  A hermitian form possessing a totally isotropic subspace of half the dimension is
hyperbolic, hence split.

Kontsevich's tropical programme (Zharkov, arXiv:2002.02347) works with a maximally degenerate
abelian `2n`-fold: `H₁ = Γ₁ ⊕ Γ₂` with `Γ₂` the lattice of vanishing cycles, `Γ₁ ≅ Γ₂*` via
the principal polarisation, both summands `E`-isotropic, and the `√-d` action preserving each.
`Γ₂ ⊗ ℚ` is then an `f`-stable, `E`-isotropic `K`-subspace of half the `K`-dimension, so by
Part A `H` vanishes identically on it: the degeneration is of **split** Weil type,
discriminant `1`, for every `n` and every value of Zharkov's parameters, since neither `E`
nor `f` involves them.  **A tropical degeneration therefore cannot reach a Weil class of
non-split discriminant, in any dimension.**

The step from "`H` vanishes on an `f`-stable isotropic half" to "`det H = (-1)ⁿ`" is classical
hermitian form theory and is **not** claimed here; what is claimed is its input, plus the fact
that the input is met by Zharkov's family for all `n` at once.

## Read-back of Part B, term by term

The index type is `Idx n = Fin 4 × Fin n`, which has exactly `4n` elements (asserted below),
identified with `Fin (4n)` by `(b, i) ↦ b * n + i`.  The four blocks are
`γ₁…γₙ`, `γ_{n+1}…γ_{2n}`, `e₁…eₙ`, `e_{n+1}…e_{2n}`; so `Γ₁` is blocks `0,1` (indices
`< 2n`) and `Γ₂`, the vanishing cycles, is blocks `2,3` (indices `≥ 2n`).

* Both `E` and `f` are `(4 × 4 pattern) ⊗ Iₙ`: they act identically on each of the `n`
  coordinate slots and mix only the four blocks.  `blk A` is that Kronecker product.
* `Eb = [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]]`, i.e. `E = [[0, I₂ₙ],[-I₂ₙ, 0]]`:
  `E(γᵢ, eⱼ) = δᵢⱼ`, `E(eⱼ, γᵢ) = -δᵢⱼ`, and `Γ₁`, `Γ₂` both isotropic.
* `Fb d = [[0,-d,0,0],[1,0,0,0],[0,0,0,-1],[0,0,d,0]] = J₁ ⊕ J₂` with
  `J₁ : γᵢ ↦ γ_{n+i}, γ_{n+i} ↦ -d γᵢ` and `J₂ : eᵢ ↦ d e_{n+i}, e_{n+i} ↦ -eᵢ`.
  Column `j` is the image of the `j`-th basis vector.  At `n = 2` this is exactly Zharkov's
  `(e₁,e₂,e₃,e₄) ↦ (d e₃, d e₄, -e₁, -e₂)` and `(γ₁,γ₂,γ₃,γ₄) ↦ (γ₃,γ₄,-d γ₁,-d γ₂)`.
* `f² = -d` → `mul F F x y = if x = y then -d else 0`.
* `f` a similitude of `E` with factor `d` → `tr F * (E * F) = d • E`.
* `E` nondegenerate → `mul E E = -1`, which forces invertibility.
* `Γ₂` isotropic and `f`-stable → the two vanishing statements on blocks `≥ 2`.
* `H` vanishes on `Γ₂` → `E x y = 0` (isotropy) together with `mul E F x y = 0` there.

## Relation to `WeilDegenerationSplit` (this problem, `s = 3`)

That statement is the case `n = 2` of Part B, written out as explicit `8 × 8` integer
matrices.  This one subsumes it, adds the coordinate-free Part A, and — the point — covers
`2n = 6, 8, 10, …` as well.  Markman (arXiv:2502.03415) is reported to settle every abelian
fourfold of Weil type; I have not read it, and nothing here depends on it.  If that and the
corresponding dimension-six results hold, the lowest dimension in which the tropical route
could still be aiming at an open case is `2n = 8` — and Part B says that what a maximal
degeneration produces there is again split.

**Attribution.**  P. Brosnan announced an observation with the same consequence in dimension
four (IBS Center for Complex Geometry, 20–21 July 2023, "How Markman Saves the Hodge
Conjecture (for Weil Type Abelian Fourfolds) from Kontsevich"); it appears never to have been
written up.  **The dimension-four case is his.**  What is new here is only that the argument
is coordinate-free and that Zharkov's data has an all-`n` block form for which the hypotheses
are verified.
-/

namespace Statements.WeilSplitIsotropic

/-- Basis index for `H₁ = Γ₁ ⊕ Γ₂` of a maximally degenerate abelian `2n`-fold.  The first
component names one of the four blocks `γ₁…γₙ | γ_{n+1}…γ_{2n} | e₁…eₙ | e_{n+1}…e_{2n}`, the
second the position inside it.  Identified with `Fin (4n)` by `(b, i) ↦ b * n + i`. -/
abbrev Idx (n : ℕ) : Type := Fin 4 × Fin n

/-- `blk A = A ⊗ Iₙ`: the `4 × 4` pattern `A` applied blockwise, acting identically on each of
the `n` coordinate slots. -/
def blk {n : ℕ} (A : Fin 4 → Fin 4 → ℤ) : Idx n → Idx n → ℤ :=
  fun x y => if x.2 = y.2 then A x.1 y.1 else 0

/-- The principal polarisation, block pattern: `E = [[0, I₂ₙ], [-I₂ₙ, 0]]`. -/
def Eb : Fin 4 → Fin 4 → ℤ := ![![0, 0, 1, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, -1, 0, 0]]

/-- The action of `√-d`, block pattern: `J₁ ⊕ J₂`, in Zharkov's normalisation. -/
def Fb (d : ℤ) : Fin 4 → Fin 4 → ℤ := ![![0, -d, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, d, 0]]

/-- Matrix product on `Idx n`. -/
def mul {n : ℕ} (A B : Idx n → Idx n → ℤ) : Idx n → Idx n → ℤ :=
  fun x z => ∑ y : Idx n, A x y * B y z

/-- Transpose. -/
def tr {n : ℕ} (A : Idx n → Idx n → ℤ) : Idx n → Idx n → ℤ := fun x y => A y x

/-- The canonical proposition.  This is the type the verifier demands. -/
abbrev statement : Prop :=
  -- Part A: dimension-free.  On an `f`-stable `E`-isotropic submodule, both components of
  -- van Geemen's hermitian form vanish.
  (∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (E : V →ₗ[R] V →ₗ[R] R) (f : V →ₗ[R] V) (d : R) (W : Submodule R V),
      (∀ x : V, E x x = 0) →                             -- `E` alternating
      (∀ x : V, f (f x) = -(d • x)) →                    -- `f² = -d`
      (∀ x y : V, E (f x) (f y) = d * E x y) →           -- `f` a similitude of `E`, factor `d`
      (∀ w ∈ W, f w ∈ W) →                               -- `W` is `f`-stable
      (∀ x ∈ W, ∀ y ∈ W, E x y = 0) →                    -- `W` is `E`-isotropic
      ∀ x ∈ W, ∀ y ∈ W, E x y = 0 ∧ E x (f y) = 0)
  ∧
  -- Part B: for every `n` and every `d`, Zharkov's maximally degenerate `2n`-fold meets those
  -- hypotheses, and the conclusion holds on its vanishing-cycle half `Γ₂`.
  (∀ (n : ℕ) (d : ℤ),
      Fintype.card (Idx n) = 4 * n
    ∧ (∀ x y : Idx n, blk Eb x y = - blk Eb y x)
    ∧ (∀ x y : Idx n, mul (blk Eb) (blk Eb) x y = if x = y then -1 else 0)
    ∧ (∀ x y : Idx n, mul (blk (Fb d)) (blk (Fb d)) x y = if x = y then -d else 0)
    ∧ (∀ x y : Idx n, mul (tr (blk (Fb d))) (mul (blk Eb) (blk (Fb d))) x y = d * blk Eb x y)
    ∧ (∀ x y : Idx n, 2 ≤ (x.1 : ℕ) → 2 ≤ (y.1 : ℕ) → blk Eb x y = 0)
    ∧ (∀ x y : Idx n, 2 ≤ (y.1 : ℕ) → (x.1 : ℕ) < 2 → blk (Fb d) x y = 0)
    ∧ (∀ x y : Idx n, 2 ≤ (x.1 : ℕ) → 2 ≤ (y.1 : ℕ) → mul (blk Eb) (blk (Fb d)) x y = 0))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.WeilSplitIsotropic
