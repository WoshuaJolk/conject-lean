import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# KontsevichWeilPhi — does Kontsevich's tropical obstruction to the Hodge conjecture exist?

This module is the **single source of truth** for what this problem means.  The verifier
reads `Statements.KontsevichWeilPhi.statement` and nothing else.  It is deliberately
self-contained: it imports only `Mathlib`, defines every object it mentions, and uses no
`Commons` module.

## The informal statement, and the term-by-term read-back

Ilia Zharkov, *Tropical abelian varieties, Weil classes and the Hodge conjecture*,
arXiv:2002.02347v1 (2020), writing up a proposal of M. Kontsevich (talk, Bogomolov 65th
birthday conference, Miami, January 2012).

Zharkov fixes a positive integer `d` and the four-parameter family of principally
polarised tropical abelian fourfolds `X_{a,b,c,e} = V / Γ₁` with polarisation matrix

```
      ⎡ a   b   0   e ⎤
  Q = ⎢ b   c  -e   0 ⎥ ,        a > 0,   d(ac - b²) - e² > 0,
      ⎢ 0  -e  da  db ⎥
      ⎣ e   0  db  dc ⎦
```

whose columns `γ₁ … γ₄` span `Γ₁` inside `Γ₂ ⊗ Γ_p`, where `Γ₂ = ℤ⟨e₁,e₂,e₃,e₄⟩` is the
lattice of integral slopes and `Γ_p = ℤ⟨a,b,c,e⟩` is the parameter lattice.  Tropical
homology in this case is `H_q(X, F_p) = ⋀^q Γ₁ ⊗ ⋀^p Γ₂`, the square of the polarisation
`θ = Σ_{i<j} γ_{ij} ⊗ e_{ij}` is a tropical Hodge `(2,2)`-class, and the two **Weil
classes** `w₁, w₂ ∈ ⋀²Γ₁ ⊗ ⋀²Γ₂` are the two extra Hodge classes coming from the
`√(-d)`-multiplication.  Whether they are represented by tropical algebraic cycles is
Kontsevich's question; a negative answer would, by specialisation to
`X_ε = (Γ₂ ⊗ ℂ*)/ε^{-1}e^{Γ₁}`, refute the classical Hodge conjecture.

Kontsevich's proposed *certificate* for a negative answer is a family of linear maps

  `Φ_{x,u} : ⋀²Γ₂ → Sym²Γ_p ⊗ Sym²(⋀²Γ₂)`,   `x ∈ (Γ₂ ⊗ Γ_p)/Γ₁`,  `u ∈ P(Γ₂ ⊗ ℚ)`,

making Zharkov's diagram commute **modulo a proper sublattice of `ℤ⟨θ, w₁, w₂⟩`**.  Such a
`Φ` kills the class of every tropical algebraic cycle (a cycle's flags have vanishing
`F₂`-components by the balancing condition), so any Hodge class outside that sublattice is
then non-algebraic.  The commutativity is Zharkov's equations (1) and (2), transcribed
verbatim below.

Read back against the Lean, term by term:

* "`d` a positive integer" → `∃ d : ℤ, 0 < d ∧ …`.  Zharkov quantifies existentially: one
  `d` suffices for a counterexample, so the existential is the honest form.
* "`Γ₂`, `Γ_p`, `Γ₂ ⊗ Γ_p`" → `G2 = Fin 4 → ℤ`, `Gp = Fin 4 → ℤ`, `G2P = Fin 4 → Fin 4 → ℤ`
  (row index = basis of `Γ₂`, column index = basis of `Γ_p`).
* "`Γ₁`" → `gammaOne d`, the `ℤ`-span of the four matrices `gammaGen d`, which are the
  columns of `Q` read as elements of `Γ₂ ⊗ Γ_p`.
* "`θ`, `w₁`, `w₂`" → `theta d`, `w1 d`, `w2 d`, built **from `Γ₁` directly** by Zharkov's
  own expansions in `⋀²Γ₁ ⊗ ⋀²Γ₂`, not from his closed forms in `Sym²Γ_p ⊗ Sym²(⋀²Γ₂)`.
  The closed forms are a computation about these classes and are therefore a theorem to be
  proved, not a definition to be trusted.
* "`Sym²Γ_p ⊗ Sym²(⋀²Γ₂)`" → the bidegree-`(2,2)` part of `T = MvPolynomial (Fin 10) ℚ`,
  with `X 0 … X 3` the parameters `a, b, c, e` and `X 4 … X 9` the six coordinates
  `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄` on `⋀²Γ₂`.  This is Zharkov's own notation.
* "`Φ` linear on `⋀²Γ₂`" → `Φ x u : Fin 6 → T` giving the six values on the basis, applied
  through `app`, so linearity is definitional rather than hypothesised.
* "`x ∈ (Γ₂ ⊗ Γ_p)/Γ₁`" → `Φ` is required to be `gammaOne d`-periodic in `x`.
* "`u ∈ P(Γ₂ ⊗ ℚ)`" → `Φ` is required to be invariant under nonzero integer rescaling of `u`.
* "equations (1) and (2)" → `triDefect` and `parDefect`, transcribed sign for sign.
* "modulo a proper sublattice of `ℤ⟨θ, w₁, w₂⟩`" → `L < weilLattice d`, with each defect
  required to lie in `L`.

**One deliberate reading.**  Zharkov states (1) and (2) "for every `u, v ∈ Γ₂`", but his
right-hand sides frame each `2`-face with `u ∧ v` while the tautological map frames it with
the *integral* volume element of the plane it spans.  These agree exactly when `u ∧ v` is a
primitive vector of `⋀²Γ₂`, and differ by the content otherwise.  The equations are
therefore imposed here only for primitive `u ∧ v` (`primBiv`).  This is the weaker system,
so a solution of it is still a solution in Kontsevich's sense, and every `2`-cell of a
tropical cycle is framed by a primitive bivector, so the obstruction argument is unaffected.

## What a solution has to do

Nothing is folded in.  Proving `statement` exhibits Kontsevich's certificate and refutes
the tropical Hodge conjecture for this family; refuting `statement` kills the route.
Zharkov's own attempt — the ansatz making `Φ_{x+su,u} - Φ_{x,u}` linear in `s` and `u` —
"does not hold modulo any proper sublattice of `ℤ⟨θ, w₁, w₂⟩`", and no stronger attempt is
recorded in the six years since.  Neither the ansatz nor its failure is assumed below.
-/

namespace Statements.KontsevichWeilPhi

open MvPolynomial

/-- `Sym²Γ_p ⊗ Sym²(⋀²Γ₂)` is realised as the bidegree-`(2,2)` part of this polynomial
ring: `X 0 … X 3` are the parameters `a, b, c, e` spanning `Γ_p`, and `X 4 … X 9` are the
coordinates `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄` of `⋀²Γ₂`. -/
abbrev T : Type := MvPolynomial (Fin 10) ℚ

/-- The four parameter variables `a, b, c, e` of `Γ_p`. -/
noncomputable def pv : Fin 4 → T := ![X 0, X 1, X 2, X 3]

/-- The six coordinates `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄` of `⋀²Γ₂`. -/
noncomputable def bv : Fin 6 → T := ![X 4, X 5, X 6, X 7, X 8, X 9]

/-- The lattice `Γ₂` of integral slopes. -/
abbrev G2 : Type := Fin 4 → ℤ

/-- The parameter lattice `Γ_p = ℤ⟨a, b, c, e⟩`. -/
abbrev Gp : Type := Fin 4 → ℤ

/-- `Γ₂ ⊗ Γ_p`, rows indexed by the basis of `Γ₂`, columns by the basis of `Γ_p`. -/
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

/-- First index of the `k`-th basis bivector, in the order `e₁₂,e₁₃,e₁₄,e₂₃,e₂₄,e₃₄`. -/
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

/-- The row of `A ∈ Γ₂ ⊗ Γ_p` at the `i`-th basis vector of `Γ₂`, as a linear form in the
parameters. -/
noncomputable def rowPoly (A : G2P) (i : Fin 4) : T := ∑ m : Fin 4, ((A i m : ℤ) : ℚ) • pv m

/-- The projection of `A ∧ B ∈ ⋀²(Γ₂ ⊗ Γ_p)` to `Sym²Γ_p ⊗ ⋀²Γ₂`. -/
noncomputable def wedgeMat (A B : G2P) : T :=
  ∑ k : Fin 6,
    (rowPoly A (bivFst k) * rowPoly B (bivSnd k) - rowPoly A (bivSnd k) * rowPoly B (bivFst k))
      * bv k

/-- The four columns of Zharkov's polarisation matrix `Q`, read as elements of `Γ₂ ⊗ Γ_p`.
They span `Γ₁`. -/
def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

/-- The period lattice `Γ₁ ⊆ Γ₂ ⊗ Γ_p`. -/
noncomputable def gammaOne (d : ℤ) : Submodule ℤ G2P :=
  Submodule.span ℤ (Set.range (gammaGen d))

/-- `θ = Σ_{i<j} γ_{ij} ⊗ e_{ij}`, the square of the polarisation. -/
noncomputable def theta (d : ℤ) : T :=
  ∑ k : Fin 6, wedgeMat (gammaGen d (bivFst k)) (gammaGen d (bivSnd k)) * bv k

/-- The first Weil class, transcribed from Zharkov's expansion in `⋀²Γ₁ ⊗ ⋀²Γ₂`
(signs resolved using `e₃₂ = -e₂₃` and `γ₃₂ = -γ₂₃`). -/
noncomputable def w1 (d : ℤ) : T :=
  let g := gammaGen d
  wedgeMat (g 0) (g 1) * bv 0
    - (1 / (d : ℚ)) • (wedgeMat (g 2) (g 3) * bv 0)
    - wedgeMat (g 0) (g 3) * bv 2
    + wedgeMat (g 0) (g 3) * bv 3
    + wedgeMat (g 1) (g 2) * bv 2
    - wedgeMat (g 1) (g 2) * bv 3
    - (d : ℚ) • (wedgeMat (g 0) (g 1) * bv 5)
    + wedgeMat (g 2) (g 3) * bv 5

/-- The second Weil class, transcribed from Zharkov's expansion in `⋀²Γ₁ ⊗ ⋀²Γ₂`. -/
noncomputable def w2 (d : ℤ) : T :=
  let g := gammaGen d
  wedgeMat (g 0) (g 3) * bv 0
    - (d : ℚ) • (wedgeMat (g 0) (g 3) * bv 5)
    - (d : ℚ) • (wedgeMat (g 0) (g 1) * bv 3)
    + wedgeMat (g 2) (g 3) * bv 3
    + (d : ℚ) • (wedgeMat (g 0) (g 1) * bv 2)
    - wedgeMat (g 2) (g 3) * bv 2
    - wedgeMat (g 1) (g 2) * bv 0
    + (d : ℚ) • (wedgeMat (g 1) (g 2) * bv 5)

/-- The lattice `ℤ⟨θ, w₁, w₂⟩` of tropical Hodge `(2,2)`-classes in play. -/
noncomputable def weilLattice (d : ℤ) : Submodule ℤ T :=
  Submodule.span ℤ {theta d, w1 d, w2 d}

/-- `u ⊗ s ∈ Γ₂ ⊗ Γ_p`; Zharkov writes this `su`. -/
def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

/-- `u ∧ v` is a primitive vector of `⋀²Γ₂`, i.e. `u` and `v` span a saturated rank-`2`
sublattice.  This is exactly when Zharkov's right-hand sides carry the integral volume
element of the plane spanned by `u` and `v`. -/
def primBiv (u v : G2) : Prop := Finset.univ.gcd (wedge u v) = 1

/-- `Φ_{x,u}` applied to a bivector given in coordinates, using linearity. -/
noncomputable def app (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) : T :=
  ∑ k : Fin 6, ((β k : ℤ) : ℚ) • Φ x u k

/-- Zharkov's equation (1), the triangle relation, as a defect that must lie in `L`:
`(Φ_{x,u} - Φ_{x,v} + Φ_{x+su,u-v} - Φ_{x+su,u} + Φ_{x+sv,v} - Φ_{x+sv,u-v})(u ∧ v)
   = s² ⊗ (u ∧ v)²`. -/
noncomputable def triDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) (u - v) (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    + app Φ (x + outer v s) v (wedge u v)
    - app Φ (x + outer v s) (u - v) (wedge u v)
    - parPoly s ^ 2 * wedgePoly u v ^ 2

/-- Zharkov's equation (2), the parallelogram relation, as a defect that must lie in `L`:
`(Φ_{x,u} - Φ_{x,v} + Φ_{x+su,v} - Φ_{x+su,u} - Φ_{x+tv,u} + Φ_{x+tv,v}
   + Φ_{x+su+tv,u} - Φ_{x+su+tv,v})(u ∧ v) = 2st ⊗ (u ∧ v)²`. -/
noncomputable def parDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s t : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) v (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    - app Φ (x + outer v t) u (wedge u v)
    + app Φ (x + outer v t) v (wedge u v)
    + app Φ (x + outer u s + outer v t) u (wedge u v)
    - app Φ (x + outer u s + outer v t) v (wedge u v)
    - (2 : ℚ) • (parPoly s * parPoly t * wedgePoly u v ^ 2)

/-- The canonical proposition.  This is the type the verifier demands.

For some positive integer `d`, Kontsevich's obstruction exists: there is a proper
sublattice `L` of `ℤ⟨θ, w₁, w₂⟩` and a family `Φ` of linear maps `⋀²Γ₂ → Sym²Γ_p ⊗
Sym²(⋀²Γ₂)`, indexed by `(Γ₂ ⊗ Γ_p)/Γ₁ × P(Γ₂ ⊗ ℚ)`, satisfying Zharkov's triangle and
parallelogram relations modulo `L`. -/
abbrev statement : Prop :=
  ∃ d : ℤ, 0 < d ∧
    ∃ (L : Submodule ℤ T) (Φ : G2P → G2 → Fin 6 → T),
      L < weilLattice d ∧
      (∀ (x : G2P) (u : G2) (g : G2P), g ∈ gammaOne d → Φ (x + g) u = Φ x u) ∧
      (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Φ x (m • u) = Φ x u) ∧
      (∀ (x : G2P) (s : Gp) (u v : G2), primBiv u v → triDefect Φ x s u v ∈ L) ∧
      (∀ (x : G2P) (s t : Gp) (u v : G2), primBiv u v → parDefect Φ x s t u v ∈ L)

/-- The open target.  Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` (or its negation) in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.KontsevichWeilPhi
