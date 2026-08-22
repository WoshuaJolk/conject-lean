import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic

/-!
# TorusNonvanishing — finitely many polynomial conditions are all satisfiable by unit phases

This is the engine of the genericity half of the copies argument, isolated from the geometry.

Context. At the target size `f_N + 1` a witness needs one *degenerate* factor: a `k`-regular
orthogonality graph in dimension `k` whose vectors are still `(k+1)`-spanning. The only published
construction (Chen–Johnston) stops at `2k` vertices, and their dominance hypothesis is exactly the
inequality saying `2k` is enough, so the reach of the classification is the reach of the gadget.
The way past the ceiling is to place several gadgets in generic relative position;
`CopiesTransversalCore` (jig.so/p/14?s=15) is the deterministic half of that, assuming
transversality and concluding tightness and spanning of the union.

What remains is the existence of a good placement, and the usual route to it is Zariski density in
the unitary group, which needs a rational parametrization of `U(k)` that does not exist off the
shelf. The observation that removes that need: a *diagonal phase* matrix `diag z` with every
`‖z r‖ = 1` preserves the Hermitian pairing exactly, hence preserves a block's orthogonality graph,
its tightness and its spanning *identically* — so the whole burden of genericity falls on the
finitely many cross conditions (no cross orthogonality, and the transversality minors). Each of
those is a polynomial in the phases: the cross pairings linearly, and each minor by Laplace
expansion into complementary column minors of the two blocks. So the geometric problem reduces to
the statement below, and the reduction consumes no topology.

The mathematical content is that the unit circle is infinite, hence Zariski-dense in the line, and
that a product of nonzero polynomials over the integral domain `ℂ` is nonzero: a nonzero polynomial
in `k` variables cannot vanish on the whole `k`-torus, because specializing one variable at a time
leaves a nonzero polynomial and a nonzero univariate polynomial has finitely many roots.

Scope. Nothing here is about vectors, graphs, unitaries or product bases: this is the substitution
principle those uses need, stated once. No claim about `ℝ` coefficients, about polynomial maps into
a finite field, or about which polynomials arise from a given geometric condition.
-/

namespace Statements.TorusNonvanishing

/-- The canonical proposition.

Given finitely many nonzero polynomials in `k` complex variables, there is a single choice of
unit-modulus values for the variables at which none of them vanishes. -/
abbrev statement : Prop :=
  ∀ (k N : ℕ) (p : Fin N → MvPolynomial (Fin k) ℂ), (∀ i, p i ≠ 0) →
    ∃ z : Fin k → ℂ, (∀ r, ‖z r‖ = 1) ∧ ∀ i, MvPolynomial.eval z (p i) ≠ 0

theorem target : statement := sorry

end Statements.TorusNonvanishing
