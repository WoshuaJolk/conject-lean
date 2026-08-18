import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# KontsevichWeilClosedForms — the closed forms of theta, w1, w2, corrected

Zharkov, *Tropical abelian varieties, Weil classes and the Hodge conjecture*,
arXiv:2002.02347v1, p.2, expands the tropical Hodge `(2,2)`-classes `theta`, `w1`, `w2` of the
family `X_{a,b,c,e}` from `⋀²Γ₁ ⊗ ⋀²Γ₂` into `Sym²Γ_p ⊗ Sym²(⋀²Γ₂)`, and states

* `theta = d(-(e/d)e₁₂ + a e₁₃ + b(e₁₄+e₂₃) + c e₂₄ - e e₃₄)²
            + D(-(1/d)e₁₂² + e₁₄² + e₂₃² - 2 e₁₃e₁₄ + d e₃₄²)`
* `w1 = D((1/√d) e₁₂ + √d e₃₄)² - D(e₁₄ + e₃₂)²`
* `w2 = 2D(e₁₂ - d e₃₄)(e₁₄ + e₃₂)`,   where `D = d(ac - b²) - e²`.

The first two are wrong.  This module states the corrected forms and the exact discrepancies,
as identities of polynomials, so that the kernel decides them rather than a reader.

Writing `P = x₁₂ - d x₃₄`, `R = x₁₄ - x₂₃`, `Pf = x₁₂x₃₄ - x₁₃x₂₄ + x₁₄x₂₃` (the Pfaffian
quadratic form on `⋀²Γ₂`) and `dL = -e x₁₂ + d(a x₁₃ + b(x₁₄+x₂₃) + c x₂₄ - e x₃₄)`, the
corrected forms are

* `d·theta = dL² + D(P² + d R² + 2d Pf)`
* `d·w1 = D P² - d D R²`
* `w2 = 2 D P R`   (Zharkov's `w2` is correct as printed),

so `theta` acquires the Pfaffian, and `w1` is `D((1/√d)x₁₂ - √d x₃₄)² - D(x₁₄+x₃₂)²` — a
**minus** sign, which is what makes `w1` and `w2` the real and imaginary parts of
`(D/d)(P + i√d R)²` and gives them the common factor `P` that the printed `w1` lacks.

The two discrepancies are recorded exactly:
`d·(theta - thetaPrinted) = 2D(x₁₂² + d x₁₃x₁₄ - d x₁₃x₂₄)` and
`w1 - w1Printed = -4D x₁₂x₃₄`.

Everything below is denominator-free: `theta`, `w2` and `d·w1` have integral coefficients, and
the identities are stated in that form.  Nothing here is asymptotic, analytic, or geometric;
it is a polynomial identity in `ℤ[a,b,c,e,d]` in disguise, and it is here so that a
mis-transcription of the period lattice would be caught by the kernel rather than by a reader.
-/

namespace Statements.KontsevichWeilClosedForms

open MvPolynomial

/-- `Sym²Γ_p ⊗ Sym²(⋀²Γ₂)` realised inside this polynomial ring: `X 0 … X 3` are the
parameters `a, b, c, e` spanning `Γ_p`; `X 4 … X 9` are the coordinates
`x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄` of `⋀²Γ₂`. -/
abbrev T : Type := MvPolynomial (Fin 10) ℚ

/-- The parameters `a, b, c, e`. -/
noncomputable def pv : Fin 4 → T := ![X 0, X 1, X 2, X 3]

/-- The coordinates `x₁₂, x₁₃, x₁₄, x₂₃, x₂₄, x₃₄`. -/
noncomputable def bv : Fin 6 → T := ![X 4, X 5, X 6, X 7, X 8, X 9]

/-- `Γ₂ ⊗ Γ_p`, rows indexed by the basis of `Γ₂`, columns by the basis of `Γ_p`. -/
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

/-- First index of the `k`-th basis bivector, in the order `e₁₂,e₁₃,e₁₄,e₂₃,e₂₄,e₃₄`. -/
def bivFst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Second index of the `k`-th basis bivector. -/
def bivSnd : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- The row of `A` at the `i`-th basis vector of `Γ₂`, as a linear form in the parameters. -/
noncomputable def rowPoly (A : G2P) (i : Fin 4) : T := ∑ m : Fin 4, (A i m : T) * pv m

/-- The projection of `A ∧ B ∈ ⋀²(Γ₂ ⊗ Γ_p)` to `Sym²Γ_p ⊗ ⋀²Γ₂`. -/
noncomputable def wedgeMat (A B : G2P) : T :=
  ∑ k : Fin 6,
    (rowPoly A (bivFst k) * rowPoly B (bivSnd k) - rowPoly A (bivSnd k) * rowPoly B (bivFst k))
      * bv k

/-- The four columns of Zharkov's polarisation matrix `Q`, as elements of `Γ₂ ⊗ Γ_p`. -/
def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

/-- `theta = Σ_{i<j} γ_{ij} ⊗ e_{ij}`, the square of the polarisation. -/
noncomputable def theta (d : ℤ) : T :=
  ∑ k : Fin 6, wedgeMat (gammaGen d (bivFst k)) (gammaGen d (bivSnd k)) * bv k

/-- `d · w1`, with `w1` the first Weil class as Zharkov expands it in `⋀²Γ₁ ⊗ ⋀²Γ₂`
(signs resolved using `e₃₂ = -e₂₃`, `γ₃₂ = -γ₂₃`); multiplying by `d` clears his `1/d`. -/
noncomputable def dw1 (d : ℤ) : T :=
  let g := gammaGen d
  (d : T) * (wedgeMat (g 0) (g 1) * bv 0)
    - wedgeMat (g 2) (g 3) * bv 0
    - (d : T) * (wedgeMat (g 0) (g 3) * bv 2)
    + (d : T) * (wedgeMat (g 0) (g 3) * bv 3)
    + (d : T) * (wedgeMat (g 1) (g 2) * bv 2)
    - (d : T) * (wedgeMat (g 1) (g 2) * bv 3)
    - (d : T) * ((d : T) * (wedgeMat (g 0) (g 1) * bv 5))
    + (d : T) * (wedgeMat (g 2) (g 3) * bv 5)

/-- The second Weil class, as Zharkov expands it in `⋀²Γ₁ ⊗ ⋀²Γ₂`. -/
noncomputable def w2 (d : ℤ) : T :=
  let g := gammaGen d
  wedgeMat (g 0) (g 3) * bv 0
    - (d : T) * (wedgeMat (g 0) (g 3) * bv 5)
    - (d : T) * (wedgeMat (g 0) (g 1) * bv 3)
    + wedgeMat (g 2) (g 3) * bv 3
    + (d : T) * (wedgeMat (g 0) (g 1) * bv 2)
    - wedgeMat (g 2) (g 3) * bv 2
    - wedgeMat (g 1) (g 2) * bv 0
    + (d : T) * (wedgeMat (g 1) (g 2) * bv 5)

/-- `D = d(ac - b²) - e²`. -/
noncomputable def Dp (d : ℤ) : T := (d : T) * (pv 0 * pv 2 - pv 1 ^ 2) - pv 3 ^ 2

/-- `P = x₁₂ - d x₃₄`. -/
noncomputable def Pp (d : ℤ) : T := bv 0 - (d : T) * bv 5

/-- `R = x₁₄ - x₂₃`  (Zharkov's `e₁₄ + e₃₂`). -/
noncomputable def Rp : T := bv 2 - bv 3

/-- The Pfaffian quadratic form `x₁₂x₃₄ - x₁₃x₂₄ + x₁₄x₂₃` on `⋀²Γ₂`. -/
noncomputable def Pfp : T := bv 0 * bv 5 - bv 1 * bv 4 + bv 2 * bv 3

/-- `d · L`, where `L = -(e/d)x₁₂ + a x₁₃ + b(x₁₄+x₂₃) + c x₂₄ - e x₃₄`. -/
noncomputable def dLp (d : ℤ) : T :=
  -(pv 3 * bv 0) + (d : T) * (pv 0 * bv 1 + pv 1 * (bv 2 + bv 3) + pv 2 * bv 4 - pv 3 * bv 5)

/-- `d ·` Zharkov's **printed** closed form for `theta`. -/
noncomputable def dthetaPrinted (d : ℤ) : T :=
  dLp d ^ 2
    + Dp d * (-bv 0 ^ 2 + (d : T) * (bv 2 ^ 2 + bv 3 ^ 2 - 2 * bv 1 * bv 2 + (d : T) * bv 5 ^ 2))

/-- `d ·` Zharkov's **printed** closed form for `w1`, i.e. `D((1/√d)x₁₂ + √d x₃₄)² - D R²`
with the denominators cleared. -/
noncomputable def dw1Printed (d : ℤ) : T :=
  Dp d * (bv 0 + (d : T) * bv 5) ^ 2 - (d : T) * (Dp d * Rp ^ 2)

/-- The canonical proposition.  This is the type the verifier demands.

For every integer `d`: the corrected closed forms of `theta`, `w1`, `w2` hold, `w2` agrees
with Zharkov's printed form, and the printed forms of `theta` and `w1` differ from the truth
by exactly the stated amounts. -/
abbrev statement : Prop :=
  ∀ d : ℤ,
    (d : T) * theta d = dLp d ^ 2 + Dp d * (Pp d ^ 2 + (d : T) * Rp ^ 2 + 2 * (d : T) * Pfp)
  ∧ dw1 d = Dp d * Pp d ^ 2 - (d : T) * (Dp d * Rp ^ 2)
  ∧ w2 d = 2 * (Dp d * Pp d * Rp)
  ∧ (d : T) * theta d - dthetaPrinted d
      = 2 * (Dp d * (bv 0 ^ 2 + (d : T) * bv 1 * bv 2 - (d : T) * bv 1 * bv 4))
  ∧ dw1 d - dw1Printed d = -4 * ((d : T) * (Dp d * bv 0 * bv 5))

/-- The open target.  A submission proves `statement` in its own module; the verifier bridges. -/
theorem target : statement := sorry

end Statements.KontsevichWeilClosedForms
