import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# KontsevichChainVolVanishes — does every balanced chain have zero tautological class?

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this asks

`KontsevichPhiSoundness` (green on this problem) proves: if `Φ` satisfies Zharkov's triangle
and parallelogram relations modulo `L`, then every **balanced chain** has its tautological
class in `L`.  Its encoding of "balanced" is

  `∀ Ψ, ∑ i ∈ s, c i * cellPhi Ψ (z i) = 0`,

i.e. the `Φ`-side of the chain vanishes **identically in `Φ`**, quantified over *all* families
`Ψ : (Γ₂ ⊗ Γ_p) → Γ₂ → Fin 6 → T` — with no periodicity, no scale invariance and no
primitivity imposed on `Ψ`.

This statement asks whether that class is not merely in `L` but always exactly `0`.  It is a
question about the encoding, not about `Φ`: `Φ` does not appear.

## Why it matters

The whole point of soundness is to convert a `Φ` into a *non-algebraic* Hodge class: a class
outside `L` cannot be the class of a chain.  That conversion has content only if some chain
has a nonzero class.  If the answer here is yes — every such chain has class `0` — then
`KontsevichPhiSoundness`, at the encoding it uses, never certifies anything: its conclusion
`∑ cᵢ · cellVol (zᵢ) ∈ L` holds for `L = ⊥` and is therefore automatic for every `L`.

The reason to expect that answer is geometric.  A tropical algebraic cycle lives in the torus
`X = V/Γ₁`; its cells are indexed by vertices **modulo `Γ₁`**, so its `Φ`-side cancels only
for families `Ψ` that are `Γ₁`-periodic.  A chain whose `Φ`-side cancels for *every* `Ψ`,
periodic or not, is a chain that already closes up in the universal cover `V`, and such a
chain bounds.  So a yes here is the precise statement that soundness must be re-encoded with
`Ψ` restricted to periodic families before it can certify anything, and that every obstruction
to Kontsevich's programme has to use the fact that `X` is a torus.

A no would be better still: it would exhibit a chain whose class is a nonzero explicit
polynomial that must then lie in `L`, and if that polynomial were outside `ℤ⟨θ, w₁, w₂⟩` the
root statement would fall with a finite certificate.

`triPhi`, `triRHS`, `parPhi`, `parRHS`, `Cell`, `cellPhi` and `cellVol` are
`KontsevichPhiSoundness`'s definitions verbatim; `triPhi - triRHS` and `parPhi - parRHS` are
the root statement's `triDefect` and `parDefect`.  Note that unlike `KontsevichPhiSoundness`
this statement imposes **no** primitivity hypothesis on the cells of the chain, so it is
asked of strictly more chains.
-/

namespace Statements.KontsevichChainVolVanishes

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

/-- The canonical proposition.  This is the type the verifier demands.

Every balanced chain has tautological class exactly zero.  "Balanced" is the encoding used by
`KontsevichPhiSoundness`: the `Φ`-side of the chain vanishes identically in `Φ`, quantified
over **all** families `Ψ`, with no periodicity, no scale invariance and no primitivity
imposed. -/
abbrev statement : Prop :=
  ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell),
    (∀ Ψ : G2P → G2 → Fin 6 → T, ∑ i ∈ s, (c i : T) * cellPhi Ψ (z i) = 0) →
    ∑ i ∈ s, (c i : T) * cellVol (z i) = 0

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.KontsevichChainVolVanishes
