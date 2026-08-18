import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# KontsevichPhiSoundness — a solution of Kontsevich's system kills every balanced chain

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this is, and why it sits on this problem

The root statement of this problem asks whether Kontsevich's obstruction `Φ` exists: a family
of linear maps satisfying Zharkov's triangle and parallelogram relations (arXiv:2002.02347,
equations (1) and (2)) modulo a proper sublattice `L` of `ℤ⟨θ, w₁, w₂⟩`.  The *reason* such a
`Φ` would be interesting is a separate claim, which Zharkov states in one sentence and does
not prove:

> "Then there will be a Hodge class `w` … which is not represented by any algebraic cycle `Z`
> under the map `vol` since all such cycles are killed by the composition `Φ ∘ α`."

That is the **soundness** of the certificate, and it is what this statement proves.  Without
it, a `Φ` would be a solution to a system of equations with no consequence attached; with it,
producing a `Φ` really does exhibit a non-algebraic Hodge class, and refuting the existence of
`Φ` really is equivalent to nothing weaker than the corresponding tropical statement.

`triPhi`, `triRHS`, `parPhi`, `parRHS` below are the two halves of the root statement's
`triDefect` and `parDefect`, split apart so that the argument can speak about them separately;
`triDefect = triPhi - triRHS` and `parDefect = parPhi - parRHS` are the root's expressions
verbatim.

## The balancing condition, and how it is encoded

A tropical algebraic cycle is a balanced weighted polyhedral complex.  Subdivided into
triangles and parallelograms it becomes a finite `ℤ`-combination of cells, and *balanced*
means that at every flag `(vertex, edge direction)` the `⋀²Γ₂`-components of the incident
`2`-faces sum to zero.  Its tautological class `vol(Z)` is then the same `ℤ`-combination of
the right-hand sides of (1) and (2).

Rather than build a flag module, balancing is encoded here as

  `∀ Ψ, ∑ i ∈ s, c i * instPhi Ψ (z i) = 0`,

i.e. the `Φ`-side of the chain vanishes **identically in `Φ`**.  This is equivalent: `instPhi Ψ`
is a fixed `ℤ`-combination of the values `Ψ x u k`, and a combination of those vanishes for
every `Ψ` exactly when each coefficient vanishes, which is exactly the balancing condition at
each flag.  Stating it this way keeps the module self-contained.

## What is claimed, and what is not

**Claimed.**  If `Φ` satisfies the triangle and parallelogram relations modulo `L` at every
instance with primitive `u ∧ v`, then for every balanced finite chain of such instances the
tautological class lies in `L`.  Consequently a Hodge class outside `L` is not the class of
any such chain.

**Not claimed, and deliberately so.**  The converse — that `L` containing every balanced
chain's class is *sufficient* for a `Φ` to exist — is **not** proved here and I do not believe
it follows.  Assigning the right-hand sides to the equation vectors is well defined on the
subgroup they generate exactly under that hypothesis, but extending that homomorphism to the
whole flag module can be obstructed, so completeness of the certificate is a genuinely
separate question.  Also not claimed: that any nonzero class is realised by a balanced chain
(the empty chain satisfies the hypothesis vacuously), the specialisation to complex abelian
fourfolds, or anything about the Hodge conjecture.
-/

namespace Submissions.KontsevichPhiSoundness.Chain

open MvPolynomial

/-- `Sym²Γ_p ⊗ Sym²(⋀²Γ₂)` realised as the bidegree-`(2,2)` part of this polynomial ring:
`X 0 … X 3` are the parameters `a, b, c, e`; `X 4 … X 9` are `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄`. -/
abbrev T : Type := MvPolynomial (Fin 10) ℚ

/-- The parameters `a, b, c, e` of `Γ_p`. -/
noncomputable def pv : Fin 4 → T := ![X 0, X 1, X 2, X 3]

/-- The coordinates `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄` of `⋀²Γ₂`. -/
noncomputable def bv : Fin 6 → T := ![X 4, X 5, X 6, X 7, X 8, X 9]

/-- The lattice `Γ₂` of integral slopes. -/
abbrev G2 : Type := Fin 4 → ℤ

/-- The parameter lattice `Γ_p`. -/
abbrev Gp : Type := Fin 4 → ℤ

/-- `Γ₂ ⊗ Γ_p`. -/
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

/-- First index of the `k`-th basis bivector, order `e₁₂,e₁₃,e₁₄,e₂₃,e₂₄,e₃₄`. -/
def bivFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Second index of the `k`-th basis bivector. -/
def bivSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- Coordinates of `u ∧ v ∈ ⋀²Γ₂`. -/
def wedge (u v : G2) (k : Fin 6) : ℤ :=
  u (bivFst k) * v (bivSnd k) - u (bivSnd k) * v (bivFst k)

/-- `u ∧ v` as a linear form in the `⋀²Γ₂` coordinates. -/
noncomputable def wedgePoly (u v : G2) : T := ∑ k : Fin 6, ((wedge u v k : ℤ) : ℚ) • bv k

/-- `s ∈ Γ_p` as a linear form in the parameters. -/
noncomputable def parPoly (s : Gp) : T := ∑ k : Fin 4, ((s k : ℤ) : ℚ) • pv k

/-- `u ⊗ s ∈ Γ₂ ⊗ Γ_p`; Zharkov writes this `su`. -/
def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

/-- `u ∧ v` is a primitive vector of `⋀²Γ₂`. -/
def primBiv (u v : G2) : Prop := Finset.univ.gcd (wedge u v) = 1

/-- `Φ_{x,u}` applied to a bivector given in coordinates, using linearity. -/
noncomputable def app (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) : T :=
  ∑ k : Fin 6, ((β k : ℤ) : ℚ) • Φ x u k

/-- A triangle instance: vertex, parameter vector, two directions. -/
abbrev TriInst : Type := G2P × Gp × G2 × G2

/-- A parallelogram instance: vertex, two parameter vectors, two directions. -/
abbrev ParInst : Type := G2P × Gp × Gp × G2 × G2

/-- The `Φ`-side of Zharkov's triangle relation (1). -/
noncomputable def triPhi (Φ : G2P → G2 → Fin 6 → T) (e : TriInst) : T :=
  app Φ e.1 e.2.2.1 (wedge e.2.2.1 e.2.2.2) - app Φ e.1 e.2.2.2 (wedge e.2.2.1 e.2.2.2)
    + app Φ (e.1 + outer e.2.2.1 e.2.1) (e.2.2.1 - e.2.2.2) (wedge e.2.2.1 e.2.2.2)
    - app Φ (e.1 + outer e.2.2.1 e.2.1) e.2.2.1 (wedge e.2.2.1 e.2.2.2)
    + app Φ (e.1 + outer e.2.2.2 e.2.1) e.2.2.2 (wedge e.2.2.1 e.2.2.2)
    - app Φ (e.1 + outer e.2.2.2 e.2.1) (e.2.2.1 - e.2.2.2) (wedge e.2.2.1 e.2.2.2)

/-- The right-hand side of Zharkov's triangle relation (1): `s² ⊗ (u ∧ v)²`. -/
noncomputable def triRHS (e : TriInst) : T :=
  parPoly e.2.1 ^ 2 * wedgePoly e.2.2.1 e.2.2.2 ^ 2

/-- The `Φ`-side of Zharkov's parallelogram relation (2). -/
noncomputable def parPhi (Φ : G2P → G2 → Fin 6 → T) (e : ParInst) : T :=
  app Φ e.1 e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ e.1 e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
    + app Φ (e.1 + outer e.2.2.2.1 e.2.1) e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ (e.1 + outer e.2.2.2.1 e.2.1) e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ (e.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.1 (wedge e.2.2.2.1 e.2.2.2.2)
    + app Φ (e.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.2 (wedge e.2.2.2.1 e.2.2.2.2)
    + app Φ (e.1 + outer e.2.2.2.1 e.2.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.1
        (wedge e.2.2.2.1 e.2.2.2.2)
    - app Φ (e.1 + outer e.2.2.2.1 e.2.1 + outer e.2.2.2.2 e.2.2.1) e.2.2.2.2
        (wedge e.2.2.2.1 e.2.2.2.2)

/-- The right-hand side of Zharkov's parallelogram relation (2): `2st ⊗ (u ∧ v)²`. -/
noncomputable def parRHS (e : ParInst) : T :=
  (2 : ℚ) • (parPoly e.2.1 * parPoly e.2.2.1 * wedgePoly e.2.2.2.1 e.2.2.2.2 ^ 2)

/-- One cell of a chain: a triangle or a parallelogram. -/
abbrev Cell : Type := TriInst ⊕ ParInst

/-- The `Φ`-side of a cell's relation. -/
noncomputable def cellPhi (Φ : G2P → G2 → Fin 6 → T) : Cell → T
  | Sum.inl e => triPhi Φ e
  | Sum.inr e => parPhi Φ e

/-- The tautological class of a cell: the right-hand side of its relation. -/
noncomputable def cellVol : Cell → T
  | Sum.inl e => triRHS e
  | Sum.inr e => parRHS e

/-- The defect of a cell's relation.  For a triangle this is the root statement's
`triDefect`, and for a parallelogram its `parDefect`, verbatim. -/
noncomputable def cellDefect (Φ : G2P → G2 → Fin 6 → T) (z : Cell) : T :=
  cellPhi Φ z - cellVol z

/-- A cell is admissible when its two directions span a primitive bivector, which is exactly
where Zharkov's relations are imposed. -/
def cellPrim : Cell → Prop
  | Sum.inl e => primBiv e.2.2.1 e.2.2.2
  | Sum.inr e => primBiv e.2.2.2.1 e.2.2.2.2

/-- The canonical proposition.  This is the type the verifier demands.

Soundness of Kontsevich's certificate: if `Φ` satisfies Zharkov's triangle and parallelogram
relations modulo `L` at every admissible instance, then every balanced finite chain of
admissible cells has its tautological class in `L`.  Balancing is `∀ Ψ, …  = 0`: the
`Φ`-side of the chain vanishes identically in `Φ`. -/
abbrev statement : Prop :=
  ∀ (L : Submodule ℤ T) (Φ : G2P → G2 → Fin 6 → T),
    (∀ z : Cell, cellPrim z → cellDefect Φ z ∈ L) →
    ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
      (∀ i ∈ s, cellPrim (z i)) →
      (∀ Ψ : G2P → G2 → Fin 6 → T, ∑ i ∈ s, (c i : T) * cellPhi Ψ (z i) = 0) →
      ∑ i ∈ s, (c i : T) * cellVol (z i) ∈ L


set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Soundness of Kontsevich's certificate.  Every cell's defect lies in `L`, so any
`ℤ`-combination of them does; that combination is the chain's `Φ`-side minus its tautological
class; and the `Φ`-side vanishes because the chain is balanced. -/
theorem proof : statement := by
  intro L Φ hdef ι s c z hprim hbal
  have h1 : ∑ i ∈ s, (c i : T) * cellDefect Φ (z i) ∈ L := by
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hx : cellDefect Φ (z i) ∈ L := hdef (z i) (hprim i hi)
    have hs : (c i) • cellDefect Φ (z i) ∈ L := L.smul_mem (c i) hx
    simpa [zsmul_eq_mul] using hs
  have h2 : ∑ i ∈ s, (c i : T) * cellDefect Φ (z i)
      = (∑ i ∈ s, (c i : T) * cellPhi Φ (z i)) - ∑ i ∈ s, (c i : T) * cellVol (z i) := by
    simp [cellDefect, mul_sub, Finset.sum_sub_distrib]
  rw [h2, hbal Φ, zero_sub] at h1
  exact (Submodule.neg_mem_iff L).mp h1

end Submissions.KontsevichPhiSoundness.Chain
