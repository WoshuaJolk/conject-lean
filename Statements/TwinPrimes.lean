import Mathlib.Data.Nat.Prime.Basic

/-!
# TwinPrimes — are there infinitely many twin primes?

This module is the **single source of truth** for what this problem means.  The verifier
reads `Statements.TwinPrimes.statement` and nothing else.  It is deliberately
self-contained: it imports only `Mathlib`, mentions only `Nat.Prime`, and uses no `Commons`
module.

## The informal statement, and the term-by-term read-back

The twin prime conjecture: there are infinitely many primes `p` such that `p + 2` is also
prime.  It is the first of the three problems Hilbert grouped as Problem 8 of his 1900 list
(alongside the Riemann hypothesis and the Goldbach conjecture), and it is usually attributed
in its general form to de Polignac (1849).

Read back against the Lean below, term by term:

* "infinitely many" → `∀ N : ℕ, ∃ p : ℕ, N < p ∧ …`.  The unbounded form, not
  `Set.Infinite`.  The two are equivalent; the explicit form is used because a submission
  must restate the proposition in its own module — it may not import this one — and an
  explicit `∀ ∃` is unambiguous to restate.
* "`p` is prime", "`p + 2` is prime" → `Nat.Prime p` and `Nat.Prime (p + 2)`, Mathlib's own
  predicate, applied to natural numbers.  Nothing is redefined here.
* There are **no hypotheses**.  A vacuous-hypothesis proof, the dominant failure mode for a
  canonical statement, is not available against this shape: there is nothing to make vacuous.

## The number the progress space tracks

Write `H₁ := liminf_{n → ∞} (p_{n+1} − p_n)`, the least gap between consecutive primes
attained infinitely often.  The conjecture above is exactly `H₁ = 2`.  The problem's progress
space is a squeeze on `H₁`, currently `2 ≤ H₁ ≤ 246`.

`H₁` is deliberately **not** the canonical statement, for a reason worth recording.  In
Mathlib, `liminf` over `ℕ` is `sSup {a | ∀ᶠ n, a ≤ u n}`, and `sSup` of an unbounded set of
naturals is `0` by convention.  So a Lean term named `H₁` denotes what a reader expects only
because the gap sequence has a bounded liminf — which is Polymath8b's theorem, and is not
formalised.  Stating the conjecture as `H₁ = 2` would therefore hide an unformalised
dependency inside the proposition.  The unbounded form above has no such dependency.

Note also that `H₁` must be a `liminf` and not an `inf`: `p₂ − p₁ = 3 − 2 = 1`, so the
infimum of the gap sequence is `1`, not `2`.  Past `n = 2` consecutive primes are odd, so
every gap is even and positive, which gives `H₁ ≥ 2` and also forces `H₁` to be even — the
live values are the `123` even numbers from `2` to `246`.

## What a solution has to do

Nothing is folded in and no partial result is assumed.  Proving `statement` settles the
conjecture.  Refuting it would show the twin primes are finite, which no one expects but
which is not excluded here.  The known partial results — Zhang's `H₁ ≤ 70000000`, Maynard's
`H₁ ≤ 600`, Polymath8b's `H₁ ≤ 246`, and the conditional bounds `H₁ ≤ 12` under
Elliott–Halberstam and `H₁ ≤ 6` under its generalisation — are all statements about `H₁`,
strictly weaker than this one, and belong as separate statements carrying their own scope.
-/

namespace Statements.TwinPrimes

/-- The canonical proposition.  This is the type the verifier demands.

There are infinitely many primes `p` for which `p + 2` is also prime: for every bound `N`
there is a prime `p > N` with `p + 2` prime. -/
abbrev statement : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- The open target.  Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimes
