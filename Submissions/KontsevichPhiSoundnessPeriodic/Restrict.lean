import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# KontsevichPhiSoundnessPeriodic — witness

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## Why this exists

`KontsevichPhiSoundness` (green on this problem) encodes "the chain is balanced" as

  `∀ Ψ, ∑ i ∈ s, c i * cellPhi Ψ (z i) = 0`,

quantified over **all** families `Ψ`.  That is strictly stronger than balancing in the torus,
and `KontsevichChainVolVanishes` shows it is too strong to be useful: every chain balanced in
that sense has tautological class exactly `0`, so the conclusion `∑ cᵢ · cellVol (zᵢ) ∈ L`
holds for `L = ⊥` and certifies nothing.

The fix is to quantify `Ψ` only over the families the root statement is about: those that are
`Γ₁`-periodic in the vertex and invariant under nonzero rescaling of the direction
(`Admissible`).  A tropical algebraic cycle in `X = V/Γ₁` has its cells indexed by vertices
*modulo* `Γ₁`, so its `Φ`-side cancels exactly for admissible `Ψ`, and not in general for
arbitrary ones.  Fewer `Ψ` to test against means more chains count as balanced, so the
hypothesis is weaker and the resulting necessary condition on `L` is stronger.

This statement is that re-encoded soundness.  It is what survives
`KontsevichChainVolVanishes`, and it is the form in which the certificate has content: a
class outside `L` is not the class of any chain balanced in the torus.

`triPhi`, `triRHS`, `parPhi`, `parRHS`, `Cell`, `cellPhi`, `cellVol`, `cellPrim` and
`cellDefect` are `KontsevichPhiSoundness`'s definitions verbatim; `gammaGen` and `gammaOne`
are the root statement's verbatim.

## What is claimed, and what is not

**Claimed.**  The implication above, for every `d`, every `L`, and every admissible `Φ`.

**Not claimed.**  That any chain balanced in the admissible sense has nonzero class — that is
the whole open question and nothing here bears on it.  Not claimed either: the converse
(completeness), the existence of any admissible `Φ`, anything about `θ`, `w₁`, `w₂`, the
specialisation to complex abelian fourfolds, or the Hodge conjecture.
-/

namespace Submissions.KontsevichPhiSoundnessPeriodic.Restrict

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

/-- `u ∧ v` is a primitive vector of `⋀²Γ₂`. -/
def primBiv (u v : G2) : Prop := Finset.univ.gcd (wedge u v) = 1

/-- A cell is admissible when its two directions span a primitive bivector. -/
def cellPrim : Cell → Prop
  | Sum.inl e => primBiv e.2.2.1 e.2.2.2
  | Sum.inr e => primBiv e.2.2.2.1 e.2.2.2.2

/-- The defect of a cell's relation: the root statement's `triDefect` / `parDefect`. -/
noncomputable def cellDefect (Φ : G2P → G2 → Fin 6 → T) (z : Cell) : T :=
  cellPhi Φ z - cellVol z

/-- The four columns of Zharkov's polarisation matrix `Q`, read as elements of `Γ₂ ⊗ Γ_p`. -/
def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

/-- The period lattice `Γ₁ ⊆ Γ₂ ⊗ Γ_p`. -/
noncomputable def gammaOne (d : ℤ) : Submodule ℤ G2P :=
  Submodule.span ℤ (Set.range (gammaGen d))

/-- A family is *admissible* when it is `Γ₁`-periodic in the vertex and invariant under
nonzero integer rescaling of the direction — exactly the two side conditions the root
statement imposes on `Φ`. -/
def Admissible (d : ℤ) (Ψ : G2P → G2 → Fin 6 → T) : Prop :=
  (∀ (x : G2P) (u : G2) (g : G2P), g ∈ gammaOne d → Ψ (x + g) u = Ψ x u) ∧
    (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Ψ x (m • u) = Ψ x u)

/-- The canonical proposition.  This is the type the verifier demands.

Soundness of Kontsevich's certificate at the *periodic* encoding of balancing: if an
admissible `Φ` satisfies Zharkov's relations modulo `L` at every admissible instance, then
every chain of admissible cells whose `Φ`-side vanishes identically **over admissible
families** has tautological class in `L`. -/
abbrev statement : Prop :=
  ∀ (d : ℤ) (L : Submodule ℤ T) (Φ : G2P → G2 → Fin 6 → T),
    Admissible d Φ →
    (∀ z : Cell, cellPrim z → cellDefect Φ z ∈ L) →
    ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
      (∀ i ∈ s, cellPrim (z i)) →
      (∀ Ψ : G2P → G2 → Fin 6 → T, Admissible d Ψ →
          ∑ i ∈ s, (c i : T) * cellPhi Ψ (z i) = 0) →
      ∑ i ∈ s, (c i : T) * cellVol (z i) ∈ L

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Instantiate the balancing hypothesis at `Ψ := Φ`, which is admissible by assumption. -/
theorem proof : statement := by
  intro d L Φ hadm hdef ι s c z hprim hbal
  have h1 : ∑ i ∈ s, (c i : T) * cellDefect Φ (z i) ∈ L := by
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hx : cellDefect Φ (z i) ∈ L := hdef (z i) (hprim i hi)
    have hs : (c i) • cellDefect Φ (z i) ∈ L := L.smul_mem (c i) hx
    simpa [zsmul_eq_mul] using hs
  have h2 : ∑ i ∈ s, (c i : T) * cellDefect Φ (z i)
      = (∑ i ∈ s, (c i : T) * cellPhi Φ (z i)) - ∑ i ∈ s, (c i : T) * cellVol (z i) := by
    simp [cellDefect, mul_sub, Finset.sum_sub_distrib]
  rw [h2, hbal Φ hadm, zero_sub] at h1
  exact (Submodule.neg_mem_iff L).mp h1

end Submissions.KontsevichPhiSoundnessPeriodic.Restrict
