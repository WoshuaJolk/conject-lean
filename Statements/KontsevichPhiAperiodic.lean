import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# KontsevichPhiAperiodic — is Zharkov's system solvable once periodicity is dropped?

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this asks, and why it sits on this problem

The root statement of this problem (`KontsevichWeilPhi`) asks for a family

  `Φ_{x,u} : ⋀²Γ₂ → Sym²Γ_p ⊗ Sym²(⋀²Γ₂)`,   `x ∈ (Γ₂ ⊗ Γ_p)/Γ₁`,  `u ∈ P(Γ₂ ⊗ ℚ)`,

satisfying Zharkov's triangle relation (1) and parallelogram relation (2) (arXiv:2002.02347)
modulo a proper sublattice `L` of `ℤ⟨θ, w₁, w₂⟩`.  It carries **three** requirements on `Φ`
beyond the two relations: linearity in the bivector (built into the type), invariance under
nonzero integer rescaling of `u`, and `Γ₁`-**periodicity** in `x`.

This statement asks the same question with the periodicity requirement, and only that
requirement, deleted — and simultaneously asks for more than the root does in three other
respects:

* the defects must be **exactly zero**, not merely in some proper sublattice `L`;
* the relations are imposed at **every** pair `u, v`, not only where `u ∧ v` is primitive;
* scale invariance in `u` is still required.

So a witness here is a `Φ` that is a legitimate Kontsevich family in every respect except
that it does not descend to the torus.  `triDefect` and `parDefect` are the root statement's
expressions verbatim.

## Why the answer is worth having either way

Soundness (`KontsevichPhiSoundness`, green on this problem) says that a `Φ` with all defects
in `L` forces every *balanced chain* — every finite `ℤ`-combination of triangle and
parallelogram instances whose `Φ`-side vanishes identically in `Φ` — to have its tautological
class in `L`.  A witness for this statement, with `L = ⊥`, therefore says that **every**
balanced chain in that sense has tautological class exactly `0`.  Balancing there is
quantified over all families `Ψ`, with no periodicity and no scale invariance imposed, so it
is exactly the notion of "a formal `ℤ`-linear relation among Zharkov's equations".

That is a hard fact about where the difficulty in Kontsevich's proposal lives.  If this
statement is true, no relation among equations (1) and (2) — no matter how long, and in
particular nothing found by solving the finite linear system Zharkov's ansatz produces —
can ever be inconsistent with the right-hand sides.  Every obstruction to Kontsevich's
certificate must then use the `Γ₁`-periodicity of `Φ`, i.e. the fact that `X = V/Γ₁` is a
torus and not a vector space.  If it is false, the equations are already formally
inconsistent and the root statement falls with a finite certificate.

Nothing here is assumed about `θ`, `w₁`, `w₂`, about `d`, or about the Hodge conjecture:
the period lattice `Γ₁` does not appear in this statement at all.
-/

namespace Statements.KontsevichPhiAperiodic

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

abbrev statement : Prop :=
  ∃ Φ : G2P → G2 → Fin 6 → T,
    (∀ (x : G2P) (u : G2) (m : ℤ), m ≠ 0 → Φ x (m • u) = Φ x u) ∧
    (∀ (x : G2P) (s : Gp) (u v : G2), triDefect Φ x s u v = 0) ∧
    (∀ (x : G2P) (s t : Gp) (u v : G2), parDefect Φ x s t u v = 0)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.KontsevichPhiAperiodic
