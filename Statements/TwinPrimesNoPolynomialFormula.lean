import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots

/-!
# TwinPrimesNoPolynomialFormula — the formula route is dead

## The elimination

A recurring attack on the twin prime conjecture is to look for a *formula*: a polynomial `f`
with integer coefficients such that `f(n)` and `f(n) + 2` are prime for every sufficiently
large `n`, or such that `f` enumerates twin-prime lower members.  This statement kills that
route outright, with a certificate rather than a plausibility argument.

Clause (i): **every** integer polynomial of degree at least `1` takes a non-prime value at
arbitrarily large arguments.  Clause (ii) is the twin-prime specialisation: for every such
`f` there are arbitrarily large `n` at which `f(n)` and `f(n) + 2` are not both prime.

`Prime` is the ring-theoretic predicate on `ℤ`, so negative primes count; that makes the
statement stronger than the `Nat.Prime` version and removes any question of sign conventions.

## Mechanism, which is the part to attack

Pick `a` with `d := f(a)` satisfying `|d| ≥ 2` — possible because `f`, `f − 1` and `f + 1`
are all nonzero polynomials and so have finitely many roots between them.  Put `D := |d|`.
For every `k`, `(a + kD) − a = kD` is divisible by `D`, and `x − y ∣ f(x) − f(y)` for any
integer polynomial, so `D ∣ f(a + kD) − d`, hence `D ∣ f(a + kD)`.  Taking `k` large enough
that `a + kD` avoids the finitely many roots of `f·(f − d)·(f + d)` makes `f(a + kD)` none of
`0, d, −d`, so `2 ≤ D < |f(a + kD)|` and `f(a + kD)` has a divisor strictly between `1` and
itself.

So the death is *arithmetic*, not analytic: a polynomial is congruence-periodic modulo any of
its own values, and the twin-prime pattern is not.  Any surviving "formula" must therefore be
non-polynomial — and the classical prime-representing polynomials (Jones–Sato–Wada–Wiens and
relatives) are consistent with this because they are multivariate and produce primes only as
their *positive* values, not at all large arguments.

## What survives

The root statement, unweakened.  The elimination removes a route, not a possibility: the
twin prime conjecture is untouched by it.

## Provenance

The single-variable case is Goldbach's observation (1752, in correspondence with Euler) that
no polynomial can represent only primes; it is standard and appears in every elementary
number theory text.  It is not in Mathlib in any form, and no formalisation of it was found.
-/

namespace Statements.TwinPrimesNoPolynomialFormula

/-- No nonconstant integer polynomial is prime-valued at all large arguments, and in
particular none generates twin prime pairs at all large arguments. -/
abbrev statement : Prop :=
  (∀ f : Polynomial ℤ, 1 ≤ f.natDegree → ∀ N : ℤ, ∃ n : ℤ, N < n ∧ ¬ Prime (f.eval n))
  ∧ (∀ f : Polynomial ℤ, 1 ≤ f.natDegree → ∀ N : ℤ, ∃ n : ℤ, N < n ∧
        ¬ (Prime (f.eval n) ∧ Prime (f.eval n + 2)))

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesNoPolynomialFormula
