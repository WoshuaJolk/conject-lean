import Mathlib.Data.Nat.Prime.Basic

/-!
# TwinPrimesNoLocalObstruction — the twin pattern has no congruence obstruction

This statement records, unconditionally and with no sieve input, that the pattern `(n, n+2)`
is *locally unobstructed*: no single congruence, and no finite set of congruences, can rule
out the existence of infinitely many `n` for which both `n` and `n + 2` avoid every small
prime.  It is the formal content of the assertion that the twin prime conjecture cannot be
**refuted** by a covering-congruence or local-solubility argument.

The fourth and third conjuncts are the **control**: they exhibit a nearby pattern for which
the very same local method *does* settle the question.  The triple `(n, n+2, n+4)` is
inadmissible at `3` — every such product is divisible by `3` — and consequently there is
exactly one prime triple of that shape, namely `(3, 5, 7)`.  So the method under discussion
is not vacuous: it decides `{0, 2, 4}` and provably fails to decide `{0, 2}`.

Read back against the Lean below, term by term.

* **(i) Admissibility of `{0,2}` at every prime.**  `∀ p, Nat.Prime p → ∃ a, ¬ p ∣ a ∧
  ¬ p ∣ (a+2)`.  For every prime `p` there is a residue class that the twin pattern may
  occupy without meeting `p`.  Equivalently `{0,2}` occupies fewer than `p` classes mod `p`
  for every prime `p`, which is exactly Hardy–Littlewood admissibility of the pair.

* **(ii) Infinitely many locally good `n`, for every modulus.**  `∀ m, 0 < m → ∀ N,
  ∃ n > N, Nat.Coprime n m ∧ Nat.Coprime (n+2) m`.  Note the order of quantifiers: `m` is
  arbitrary and the conclusion is unbounded in `n`.  So no modulus, however large — in
  particular no product of the primes below any bound — kills the pattern.  A covering
  system argument against the twin primes would have to falsify this for some `m`.

* **(iii) The triple `{0,2,4}` is inadmissible at `3`.**  `∀ a, 3 ∣ a * (a+2) * (a+4)`.
  Here the local method bites.

* **(iv) The consequence.**  `∀ p, Nat.Prime p → Nat.Prime (p+2) → Nat.Prime (p+4) →
  p = 3`.  Exactly one prime triple of shape `(p, p+2, p+4)` exists.  This is what a
  successful local obstruction looks like, and (i) and (ii) say it is unavailable for
  `{0,2}`.

## What this does and does not say

It does **not** advance any bound on `H₁`, and it is not evidence for the twin prime
conjecture.  What it does is remove a route: an elimination of the search for a
congruence-theoretic refutation, leaving the conjecture itself standing untouched.  The
obstruction to the conjecture is not local.
-/

namespace Statements.TwinPrimesNoLocalObstruction

/-- The canonical proposition.  Four unconditional arithmetic facts: the pair `{0,2}` is
admissible at every prime; for every modulus `m` there are arbitrarily large `n` with `n`
and `n+2` both coprime to `m`; the triple `{0,2,4}` is inadmissible at `3`; and hence
`(3,5,7)` is the only prime triple of shape `(p, p+2, p+4)`. -/
abbrev statement : Prop :=
  (∀ p : ℕ, Nat.Prime p → ∃ a : ℕ, ¬ p ∣ a ∧ ¬ p ∣ (a + 2)) ∧
  (∀ m : ℕ, 0 < m → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Coprime n m ∧ Nat.Coprime (n + 2) m) ∧
  (∀ a : ℕ, 3 ∣ a * (a + 2) * (a + 4)) ∧
  (∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) → Nat.Prime (p + 4) → p = 3)

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesNoLocalObstruction
