import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth

/-!
# TwinPrimesGapParity — every gap between odd primes is even and at least 2

Self-contained: imports only `Mathlib`, mentions only `Nat.Prime`, `Nat.nth` and `Even`,
uses no `Commons`.

## What is claimed

The elementary floor under problem 9's progress space.  Two forms of one fact, plus the
data that shows both hypotheses are load-bearing.

**The pair form.**  For any two primes `p < q` with `p > 2`, the difference `q - p` is even
and at least `2`.  The `2 < p` is the whole hypothesis: past `2` every prime is odd, so any
difference of two of them is even, and it is nonzero because `p < q`.  Note that this is
*stronger* than the same claim for **consecutive** primes — no "there is no prime strictly
between" hypothesis is carried, because none is needed.  A statement that carried one would
be weaker and would invite the reader to think the consecutiveness is doing work.

**The indexed form.**  On Mathlib's `Nat.nth Nat.Prime`, which is **0-indexed**
(`Nat.nth Nat.Prime 0 = 2`), the successive differences
`Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n` are even and at least `2` for every
`n ≥ 1`.  The enumeration is also asserted to be prime-valued and strictly increasing, so
that "gap" means what it should: `Nat.nth` of a *finite* predicate is eventually constant,
and strict monotonicity is exactly what rules that out here.  Strict monotonicity rests on
the infinitude of the primes (Euclid), which Mathlib has as
`Nat.infinite_setOfPred_prime`.

**Why `n ≥ 1` and not `n ≥ 0`.**  Because the claim is false at `n = 0`:
`Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0 = 3 - 2 = 1`, which is odd.  That single
exception is asserted here, negation and all.  It is the reason `H₁` has to be a `liminf`
and not an `inf`: the infimum of the gap sequence is `1`, attained once.  And the bound `2`
is attained — `Nat.nth Nat.Prime 3 - Nat.nth Nat.Prime 2 = 7 - 5 = 2` — so `2 ≤ ·` is sharp
and the statement is not a bound that could be raised for free.

## What this buys the problem, exactly

`H₁ := liminf_{n → ∞} (p_{n+1} − p_n)`.  The problem's snapshot carries `lower = 2` at proof
grade; this statement is what that number rests on.  Every gap past the first is even and
`≥ 2`, so `H₁ ≥ 2`, and `H₁` — being a value attained infinitely often by an eventually-even
sequence — is even; with the unconditional ceiling `H₁ ≤ 246` (Polymath8b Thm 1.4(i)) only
the `123` even values `2, 4, …, 246` are live.

Be precise about the residue.  What is formalised here is the statement about the gap
**sequence**.  The step from "the sequence is eventually even and `≥ 2`" to "`H₁` is even
and `≥ 2`" is *not* formalised, and deliberately so: `liminf` over `ℕ` in Mathlib is
`sSup {a | ∀ᶠ n, a ≤ u n}`, and `sSup` of an unbounded set of naturals is `0` by convention,
so a Lean term named `H₁` means what a reader expects only given that the gap sequence has
bounded liminf — Polymath8b's theorem, which is not formalised anywhere.  Writing `H₁` into
a Lean proposition would import that unformalised dependency; the root statement of this
problem avoids it for the same reason.  So this statement says the arithmetic, and the
arithmetic is what a reader can check; the `liminf` bookkeeping stays in prose, where its
dependency is visible.

## What is not claimed

Nothing about infinitude of twin primes, nothing about any upper bound on `H₁`, and nothing
about consecutive primes beyond what the pair form already gives.
-/

namespace Statements.TwinPrimesGapParity

/-- The canonical proposition: every difference of two primes above `2` is even and at least
`2`; the same for the successive differences of `Nat.nth Nat.Prime` from index `1` on, that
enumeration being prime-valued and strictly increasing; and the two pieces of data that make
the hypotheses load-bearing — the odd gap `1` at index `0`, and the gap `2` at index `2`,
which shows the bound is sharp. -/
abbrev statement : Prop :=
  -- the pair form: no consecutiveness hypothesis is needed
  (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → p < q → 2 ≤ q - p ∧ Even (q - p))
  -- the enumeration is prime-valued and strictly increasing
  ∧ (∀ n : ℕ, Nat.Prime (Nat.nth Nat.Prime n))
  ∧ (∀ n : ℕ, Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1))
  -- the indexed form, from index 1 on
  ∧ (∀ n : ℕ, 1 ≤ n →
        2 ≤ Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n
      ∧ Even (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n))
  -- index 0 is the genuine exception: the gap there is 1, and it is odd
  ∧ (Nat.nth Nat.Prime 0 = 2 ∧ Nat.nth Nat.Prime 1 = 3
      ∧ Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0 = 1
      ∧ ¬ Even (Nat.nth Nat.Prime 1 - Nat.nth Nat.Prime 0))
  -- and the bound 2 is attained, so it is sharp
  ∧ (Nat.nth Nat.Prime 2 = 5 ∧ Nat.nth Nat.Prime 3 = 7
      ∧ Nat.nth Nat.Prime 3 - Nat.nth Nat.Prime 2 = 2)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesGapParity
