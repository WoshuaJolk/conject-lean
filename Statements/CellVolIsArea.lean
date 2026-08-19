import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# CellVolIsArea — Zharkov's right-hand sides are (area 2-vector) ⊗ (framing), and shoelace

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this says

Zharkov's relations (1) and (2) have right-hand sides `s² ⊗ (u ∧ v)²` and `2st ⊗ (u ∧ v)²`.
Read geometrically, the triangle with vertex `x` and edge vectors `p = u ⊗ s`, `q = v ⊗ s`
has `p ∧ q` for twice its oriented area, and `u ∧ v` for its framing in `⋀²Γ₂`; likewise the
parallelogram with `p = u ⊗ s`, `q = v ⊗ t`.  The first two clauses below say that the
right-hand sides are exactly

  `wedgeMat p q · (u ∧ v)^`   and   `2 · wedgeMat p q · (u ∧ v)^`,

where `wedgeMat` is the projection of `⋀²(Γ₂ ⊗ Γ_p)` to `Sym²Γ_p ⊗ ⋀²Γ₂`.  So `cellVol` is
the tautological class `(2 × area) ⊗ (framing)` of the cell, not merely a formal expression.

The last two clauses are the **shoelace identities** for the boundaries that the `Φ`-sides of
(1) and (2) run over.  Reading the six flags of `triPhi` as the endpoints of the three
oriented edges `-(x,p) + (x,q) + (x+q, p-q)`, and the eight flags of `parPhi` as those of
`-(x,p) + (x+q,p) + (x,q) - (x+p,q)`, the alternating sum of `wedgeMat(tail, displacement)`
over the boundary is `-wedgeMat p q` and `-2 wedgeMat p q` respectively — the discrete
Stokes theorem for the constant `2`-form, in the exact combinatorial shape the flag system
uses.

Together these two facts are step 1 of the argument recorded on `ChainVolSymGammaOne`
(p/8?s=21): they turn the balancing condition, which is a statement about flags, into a
statement about oriented areas, which is what makes the whole endgame go.

## Read-back

* `triRHS`, `parRHS`, `wedgeMat`, `outer`, `wedgePoly`, `parPoly`, `rowPoly` are transcribed
  from the root statement `KontsevichWeilPhi` without change.
* `2 X` is written `X + X` so that no scalar action appears.
* Nothing is claimed about balancing, about `Γ₁`, or about the class of a chain.
-/

namespace Statements.CellVolIsArea

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

noncomputable def wedgeMat (A B : G2P) : T :=
  ∑ k : Fin 6,
    (rowPoly A (bivFst k) * rowPoly B (bivSnd k) - rowPoly A (bivSnd k) * rowPoly B (bivFst k))
      * bv k

def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

abbrev TriInst : Type := G2P × Gp × G2 × G2
abbrev ParInst : Type := G2P × Gp × Gp × G2 × G2

noncomputable def triRHS (e : TriInst) : T :=
  parPoly e.2.1 ^ 2 * wedgePoly e.2.2.1 e.2.2.2 ^ 2

noncomputable def parRHS (e : ParInst) : T :=
  (2 : ℚ) • (parPoly e.2.1 * parPoly e.2.2.1 * wedgePoly e.2.2.2.1 e.2.2.2.2 ^ 2)

/-- The canonical proposition.  This is the type the verifier demands.

Zharkov's right-hand sides are the projected area `2`-vector of the cell times its framing;
and the alternating sum of `wedgeMat(tail, displacement)` over the boundary of a triangle,
resp. a parallelogram, recovers that `2`-vector. -/
abbrev statement : Prop :=
  (∀ (x : G2P) (s : Gp) (u v : G2),
      triRHS (x, s, u, v) = wedgeMat (outer u s) (outer v s) * wedgePoly u v) ∧
  (∀ (x : G2P) (s t : Gp) (u v : G2),
      parRHS (x, s, t, u, v) = wedgeMat (outer u s) (outer v t) * wedgePoly u v
        + wedgeMat (outer u s) (outer v t) * wedgePoly u v) ∧
  (∀ x p q : G2P,
      wedgeMat x q + wedgeMat (x + q) (p - q) + wedgeMat p q = wedgeMat x p) ∧
  (∀ x p q : G2P,
      wedgeMat (x + q) p + wedgeMat x q + wedgeMat p q + wedgeMat p q
        = wedgeMat x p + wedgeMat (x + p) q)

/-- The open target.  A submission proves `statement` in its own module; the verifier bridges
the two. -/
theorem target : statement := sorry

end Statements.CellVolIsArea
