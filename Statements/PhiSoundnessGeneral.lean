import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# PhiSoundnessGeneral — Kontsevich's certificate is sound in every cell dimension

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The claim in one line

If a family `Φ` satisfies the `p`-dimensional cell relations modulo a subgroup `L`, then the
tautological class of every **balanced** finite chain of admissible `p`-cells lies in `L`.
Hence a Hodge class outside `L` is the class of no such chain: `Φ` is a sound obstruction.

## Why this statement exists, and what it generalises

The root statement of this problem (`KontsevichWeilPhi`) asks whether Kontsevich's obstruction
`Φ` exists for Zharkov's triangle and parallelogram relations (arXiv:2002.02347, equations (1)
and (2)) modulo a proper sublattice `L`.  `KontsevichPhiSoundness` (p/8?s=4) proves that a
solution really does obstruct: it kills the tautological class of every balanced chain.  That
statement is written for **`2`-dimensional** cells, because Zharkov writes only the case of an
abelian fourfold, where a Weil class is a `(2,2)`-class and the cycles that could represent it
are `2`-dimensional.

The programme's live case is the abelian **eightfold**, where a Weil class is a `(4,4)`-class
and the cells are `4`-dimensional.  There the generating cells are no longer "triangles and
parallelograms": they are the products of simplices `Δ^{p₁} × ⋯ × Δ^{p_k}`, one per partition
`p = p₁ + ⋯ + p_k` (five of them at `p = 4`), each carrying one parameter vector `σ_j ∈ Γ_p`
per factor; and `Φ` is no longer indexed by a vertex and a single edge direction but by a
vertex together with the **complete slope flag** `V₁ ⊂ ⋯ ⊂ V_{p-1}` of the cell's faces, `Φ`
remaining linear in the top volume element in `⋀^p Γ₂`.  (Every proper coarsening of that flag
makes the relation the vacuous `0 = 0` at `p ≥ 3`, so the flag really is forced.)

**None of that enters the soundness argument.**  The argument is eight lines of module algebra
and never mentions the dimension: each admissible cell's defect lies in `L`, so any integer
combination of defects does; that combination is the chain's `Φ`-side minus its tautological
class; and the `Φ`-side vanishes because the chain is balanced.  This statement is that
argument, stated once for every `p`.  Proving it discharges soundness for Zharkov's `p = 2`
**and** for the `p = 4` system at the same time, so that any future `p = 4` relation-set is
meaningful the moment it is written down.

## How the `p`-dimensional data is encoded, and how to read it back

Fix `N`, the rank of the slope lattice `Γ₂` (`N = 2n` for an abelian `2n`-fold), `m`, the rank
of the parameter lattice `Γ_p` (`m = n²`), and `p`, the cell dimension (`p = n`).

* `G2 N = Fin N → ℤ` is `Γ₂`; `G2P N m = Fin N → Fin m → ℤ` is `Γ₂ ⊗ Γ_p`, where the vertices
  `F₀` live (Zharkov's `x`, taken modulo the period lattice `Γ₁` by the caller).
* `Flag N p = Fin (p-1) → G2 N` is the flag datum `V₁ ⊂ ⋯ ⊂ V_{p-1}`, presented by an ordered
  spanning sequence `w₁, …, w_{p-1}` of `Γ₂`-vectors with `V_r = ⟨w₁, …, w_r⟩`.  At `p = 2`
  this is a single direction — exactly Zharkov's `F₁ ∈ P(Γ₂ ⊗ ℚ)`.  At `p = 4` it is a point of
  `Fl(1,2,3; ℚ^8)`.
* `Biv N p = Fin (N.choose p) → ℤ` is `⋀^p Γ₂` in coordinates; `N.choose p` is `6` at
  `(N,p) = (4,2)`, matching `KontsevichPhiSoundness`, and `70` at `(N,p) = (8,4)`.
* `Φ : G2P N m → Flag N p → Fin (N.choose p) → M` is the family, and `app` extends it linearly
  in the `⋀^p Γ₂` argument, exactly as `app` does in `KontsevichPhiSoundness`.
* A `Cell` is presented **by its relation's left-hand side**: a finite list of signed
  `(coefficient, vertex, flag)` terms together with the volume element `vol ∈ ⋀^p Γ₂` at which
  `Φ` is evaluated.  `cellPhi` is the resulting signed flag sum.  This is the shape of every
  relation in the family: Zharkov's (1) is the `6`-term list of a `Δ²`, his (2) the `8`-term
  list of a `Δ¹ × Δ¹`, and at `p = 4` the five cells give lists of `120`, `192`, `216`, `288`
  and `384` terms.  In general a `Δ^{p₁} × ⋯ × Δ^{p_k}` contributes `p! ∏_j (p_j + 1)` terms.
* `taut z` is the right-hand side, the cell's tautological class: `s² ⊗ (u∧v)²` for Zharkov's
  triangle, `2st ⊗ (u∧v)²` for his parallelogram, and `(p!/∏_j p_j!) (∏_j σ_j^{p_j}) ⊗ Ω_cell·Ω`
  in general.  `M` is the ambient module — `Sym^p Γ_p ⊗ Sym²(⋀^p Γ₂)` in the application — and
  is left abstract because nothing in the argument uses its structure.
* `adm z` is admissibility: the hypothesis under which the relation is imposed (Zharkov imposes
  his at primitive `u ∧ v`; at `p ≥ 3` one also asks that the cell's slopes span a
  `p`-dimensional subspace, degenerate cells contributing `0 = 0`).  Left abstract for the same
  reason.

Nothing is assumed about `terms`, `vol`, `taut` or `adm`: the statement holds for *whatever*
the correct `p`-dimensional relation set turns out to be, which is the point — it is the part
of the programme that does not have to wait for the flag combinatorics to be pinned down.

## The balancing condition, and why it is stated as it is

A tropical algebraic cycle is a balanced weighted polyhedral complex; subdivided into the
generating cells it is a finite `ℤ`-combination `∑ᵢ cᵢ zᵢ`, and *balanced* means that at every
flag `(vertex, V₁ ⊂ ⋯ ⊂ V_{p-1})` the `⋀^p Γ₂`-components of the incident `p`-faces sum to
zero.  Rather than build a flag module, balancing is encoded here as

  `∀ Ψ, ∑ i ∈ s, c i • cellPhi Ψ (z i) = 0`,

i.e. the `Φ`-side of the chain vanishes **identically in `Φ`**.  This is equivalent: by
construction `cellPhi Ψ z` is a fixed `ℤ`-combination of the values `Ψ x f k`, and such a
combination vanishes for every `Ψ` exactly when each coefficient does, which is exactly
balancing at each flag.  Stating it this way keeps the module self-contained and is the same
encoding `KontsevichPhiSoundness` uses at `p = 2`.

## What is claimed, and what is not

**Claimed.**  Soundness, for every cell dimension: relations modulo `L` at every admissible
cell force every balanced chain's tautological class into `L`.

**Not claimed, and deliberately so.**

* **Completeness.**  That `L` containing every balanced chain's class suffices for a `Φ` to
  exist is *not* proved and I do not believe it follows: assigning right-hand sides to the
  equation vectors is well defined on the subgroup they generate under that hypothesis, but
  extending that homomorphism to the whole flag module can be obstructed.
* **Non-vacuity of any particular instance.**  The empty chain satisfies the hypothesis, and
  nothing here says a nonzero class is realised by a balanced chain, or that a `Φ` exists at
  `p = 2` or `p = 4`.
* **That the `p = 4` relation set stated elsewhere is the right one.**  This statement is
  deliberately parametric in `terms`, `vol`, `taut` and `adm` precisely so that it does not
  depend on that; the flag/product-of-simplices analysis is a separate claim.
* Anything about complex abelian varieties, tropical-to-classical comparison, or the Hodge
  conjecture.
-/

namespace Statements.PhiSoundnessGeneral

/-- The lattice `Γ₂` of integral slopes, of rank `N`. -/
abbrev G2 (N : ℕ) : Type := Fin N → ℤ

/-- `Γ₂ ⊗ Γ_p` with `Γ_p` of rank `m`: the lattice the vertices `F₀` live in, before the
quotient by the period lattice `Γ₁`. -/
abbrev G2P (N m : ℕ) : Type := Fin N → Fin m → ℤ

/-- The flag datum of a `p`-dimensional cell: the complete slope flag `V₁ ⊂ ⋯ ⊂ V_{p-1}`,
presented by an ordered spanning sequence, `V_r = ⟨w₁, …, w_r⟩`.  At `p = 2` this is a single
direction, Zharkov's `F₁`. -/
abbrev Flag (N p : ℕ) : Type := Fin (p - 1) → G2 N

/-- `⋀^p Γ₂` in coordinates.  `N.choose p` is `6` at `(N,p) = (4,2)` and `70` at `(8,4)`. -/
abbrev Biv (N p : ℕ) : Type := Fin (N.choose p) → ℤ

/-- A family `Φ_{F₀ ; V₁ ⊂ ⋯ ⊂ V_{p-1}} : ⋀^p Γ₂ → M`, given on the coordinate basis. -/
abbrev PhiFam (N m p : ℕ) (M : Type) : Type := G2P N m → Flag N p → Fin (N.choose p) → M

/-- `Φ_{x ; f}` applied to a `p`-vector given in coordinates, using linearity. -/
noncomputable def app {N m p : ℕ} {M : Type} [AddCommGroup M]
    (Φ : PhiFam N m p M) (x : G2P N m) (f : Flag N p) (β : Biv N p) : M :=
  ∑ k : Fin (N.choose p), β k • Φ x f k

/-- A `p`-dimensional cell, presented by the left-hand side of its relation.  `z.1` is the
signed list of `(coefficient, vertex, flag)` terms of the cell's flag sum, and `z.2` is the
volume element of `⋀^p Γ₂` at which `Φ` is evaluated — the primitive generator of `⋀^p` of the
cell's slope lattice. -/
abbrev Cell (N m p : ℕ) : Type := List (ℤ × G2P N m × Flag N p) × Biv N p

/-- The `Φ`-side of a cell's relation: its signed flag sum. -/
noncomputable def cellPhi {N m p : ℕ} {M : Type} [AddCommGroup M]
    (Φ : PhiFam N m p M) (z : Cell N m p) : M :=
  (z.1.map fun t => t.1 • app Φ t.2.1 t.2.2 z.2).sum

/-- The canonical proposition.  This is the type the verifier demands.

Soundness of Kontsevich's certificate in cell dimension `p`: if `Φ` satisfies the cell relations
modulo `L` at every admissible cell, then every balanced finite chain of admissible cells has
its tautological class in `L`.  Balancing is `∀ Ψ, … = 0`: the `Φ`-side of the chain vanishes
identically in `Φ`. -/
abbrev statement : Prop :=
  ∀ (N m p : ℕ) (M : Type) [_inst : AddCommGroup M]
    (taut : Cell N m p → M) (adm : Cell N m p → Prop)
    (L : Submodule ℤ M) (Φ : PhiFam N m p M),
      (∀ z : Cell N m p, adm z → cellPhi Φ z - taut z ∈ L) →
      ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell N m p),
        (∀ i ∈ s, adm (z i)) →
        (∀ Ψ : PhiFam N m p M, ∑ i ∈ s, c i • cellPhi Ψ (z i) = 0) →
        ∑ i ∈ s, c i • taut (z i) ∈ L

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.PhiSoundnessGeneral
