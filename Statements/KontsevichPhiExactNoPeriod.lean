import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# KontsevichPhiExactNoPeriod — Kontsevich's system is exactly solvable once periodicity is dropped

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this is

The root statement of this problem (`KontsevichWeilPhi`) asks for a family of linear maps
`Φ_{x,u} : ⋀²Γ₂ → Sym²Γ_p ⊗ Sym²(⋀²Γ₂)` satisfying **five** conditions:

1. `Φ` is `Γ₁`-periodic in `x`;
2. `Φ` is invariant under nonzero integer rescaling of `u`;
3. Zharkov's triangle relation (1) holds modulo `L`;
4. Zharkov's parallelogram relation (2) holds modulo `L`;
5. `L` is a **proper** sublattice of `ℤ⟨θ, w₁, w₂⟩`.

This statement says that conditions 2, 3 and 4 alone are satisfiable **on the nose** — with
`L = 0`, with no primitivity restriction on `u ∧ v`, and for every `x`, `s`, `t`, `u`, `v`.
Consequently the entire content of Kontsevich's question is condition 1: the whole
obstruction is `Γ₁`-periodicity, and nothing else.

`triDefect` and `parDefect` below are the root statement's expressions **verbatim**, with the
same `app`, `outer`, `wedge`, `wedgePoly` and `parPoly`.  The only differences from the root
are that `Γ₁`-periodicity is not asked for, that `L` is `0` rather than a sublattice, and that
the relations are demanded at **every** pair `u, v` rather than only at primitive `u ∧ v` —
each of which makes this statement a strictly stronger demand on the two relations themselves.

## Why it matters, and what it does not claim

Zharkov (arXiv:2002.02347) reports that his ansatz — `λ_{x,s,u} = Φ_{x+su,u} - Φ_{x,u}` taken
linear in `s` and in `u` — "does not hold modulo any proper sublattice of `ℤ⟨θ, w₁, w₂⟩`", and
identifies the difficulty as making `λ_{x,·,·}` well defined modulo `Γ₁`.  This statement
isolates that difficulty exactly: before `Γ₁` enters, the system is not merely solvable modulo
`ℤ⟨θ, w₁, w₂⟩`, it is solvable with zero defect, and a witness can be written in closed form.
So no lower bound on `L` can come from the relations alone; every such bound must come from
periodicity.

**Not claimed.** Nothing here says a `Γ₁`-periodic solution exists, for any `L`.  Nothing here
says `L` can be made proper.  Nothing here is about the Hodge conjecture.  The witness used in
the proof is *not* `Γ₁`-periodic and, since `θ` is an algebraic class, no solution with `L = 0`
can be.
-/

namespace Statements.KontsevichPhiExactNoPeriod

open MvPolynomial

/-- `Sym²Γ_p ⊗ Sym²(⋀²Γ₂)` realised as the bidegree-`(2,2)` part of this polynomial ring:
`X 0 … X 3` are the parameters `a, b, c, e`; `X 4 … X 9` are `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄`. -/
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

/-- `u ⊗ s ∈ Γ₂ ⊗ Γ_p`; Zharkov writes this `su`. -/
def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

/-- `Φ_{x,u}` applied to a bivector given in coordinates, using linearity. -/
noncomputable def app (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (u : G2) (β : Fin 6 → ℤ) : T :=
  ∑ k : Fin 6, ((β k : ℤ) : ℚ) • Φ x u k

/-- Zharkov's equation (1), the triangle relation, as a defect.  Verbatim from the root
statement `KontsevichWeilPhi`. -/
noncomputable def triDefect (Φ : G2P → G2 → Fin 6 → T) (x : G2P) (s : Gp) (u v : G2) : T :=
  app Φ x u (wedge u v) - app Φ x v (wedge u v)
    + app Φ (x + outer u s) (u - v) (wedge u v)
    - app Φ (x + outer u s) u (wedge u v)
    + app Φ (x + outer v s) v (wedge u v)
    - app Φ (x + outer v s) (u - v) (wedge u v)
    - parPoly s ^ 2 * wedgePoly u v ^ 2

/-- Zharkov's equation (2), the parallelogram relation, as a defect.  Verbatim from the root
statement `KontsevichWeilPhi`. -/
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

Dropping `Γ₁`-periodicity, Kontsevich's system is solvable exactly: there is a family `Φ` of
linear maps `⋀²Γ₂ → Sym²Γ_p ⊗ Sym²(⋀²Γ₂)`, indexed by `Γ₂ ⊗ Γ_p` and by `P(Γ₂ ⊗ ℚ)`
(i.e. invariant under nonzero integer rescaling of `u`), whose triangle and parallelogram
defects vanish identically — at every `x`, `s`, `t` and **every** pair `u, v`, primitive or
not. -/
abbrev statement : Prop :=
  ∃ Φ : G2P → G2 → Fin 6 → T,
    (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Φ x (m • u) = Φ x u) ∧
    (∀ (x : G2P) (s : Gp) (u v : G2), triDefect Φ x s u v = 0) ∧
    (∀ (x : G2P) (s t : Gp) (u v : G2), parDefect Φ x s t u v = 0)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.KontsevichPhiExactNoPeriod
