import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# TwinPrimesClementDead — Clement's congruence is the conjecture, not a route to it

Self-contained: imports only `Mathlib`, mentions only `Nat.Prime` and `Nat.factorial`, uses
no `Commons`.

## The route this eliminates

Clement (1949) proved an elementary criterion for twin primality: for `n ≥ 2`,

  `n` and `n + 2` are both prime  ⟺  `n(n + 2) ∣ 4((n − 1)! + 1) + n`.

It is the best-known member of a recurring family of attacks — restate the twin prime
conjecture as a single arithmetic congruence via Wilson's theorem, then try to count its
solutions by elementary means.  The attraction is real: the right-hand side mentions no
primality predicate at all, only a factorial and a divisibility, so it looks like a problem
about the growth of `n!` rather than a problem about primes.

This statement records why that appearance is false, with a certificate.  The criterion is
an **equivalence**, so the set of `n ≥ 2` satisfying the congruence is *equal* to the set of
lower twin-prime members, and — the conjunct that does the eliminating —

  `(∀ N, ∃ p > N, p and p + 2 prime)  ↔  (∀ N, ∃ n > N, n ≥ 2 ∧ n(n+2) ∣ 4((n−1)!+1) + n)`

both directions, kernel-checked.  The Clement infinitude statement is not a weakening of
the twin prime conjecture, not a strengthening, and not a reduction: it **is** the twin
prime conjecture, character for character in truth value.  Any argument that would settle
one settles the other, so no work is saved by passing through the congruence, and a
transformation which preserves truth value exactly cannot lower difficulty.

That is the elimination, and it is narrow on purpose.  What dies is the hope that
Wilson-type congruence reformulation is a *reduction*.  What is untouched is the twin prime
conjecture itself, which is this statement's `residual_of`: the route leaves the root exactly
where it found it, which is the whole content of the finding.

## Read-back, term by term

* `(n - 1)!` is `Nat.factorial (n - 1)` with **truncated** natural subtraction.  The `2 ≤ n`
  hypothesis makes it harmless: the proof substitutes `n = k + 2` immediately, after which no
  subtraction appears anywhere.  Without `2 ≤ n` the criterion is false at `n = 0`
  (`0 * 2 = 0` divides nothing but `0`, while `4(0! + 1) + 0 = 8`), so the hypothesis is
  load-bearing rather than cosmetic.
* The second conjunct's right-hand side carries `2 ≤ n` explicitly, so it is a statement about
  the same `n` the criterion is proved for.
* The last four conjuncts are the kernel's own forced-answer controls on the criterion, in
  **both** directions.  `n = 3` and `n = 11` are twin lower members and the congruence holds;
  `n = 7` is prime but `9` is not, and it fails; `n = 9` is not prime, and it fails.  A
  criterion that accepted everything would be caught by the two negative cases, and one that
  accepted nothing by the two positive cases.

## What is not claimed

No bound on `H₁` moves, no progress snapshot accompanies this, and nothing here is evidence
for or against the conjecture.  It is not claimed that all elementary approaches are dead,
nor that Wilson's theorem is useless in analytic number theory — only that *this* particular
change of variables is truth-preserving and therefore cannot be a reduction.
-/

namespace Statements.TwinPrimesClementDead

open Nat

/-- The canonical proposition: Clement's criterion for `n ≥ 2`, both directions; the
resulting equivalence between the twin prime conjecture and the infinitude of solutions of
the congruence, both directions; and four numeric controls, two positive and two negative. -/
abbrev statement : Prop :=
  (∀ n : ℕ, 2 ≤ n →
      ((Nat.Prime n ∧ Nat.Prime (n + 2)) ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n))
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
      ↔ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ 2 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n))
  ∧ (3 * 5 ∣ 4 * ((3 - 1)! + 1) + 3)
  ∧ (11 * 13 ∣ 4 * ((11 - 1)! + 1) + 11)
  ∧ ¬ (7 * 9 ∣ 4 * ((7 - 1)! + 1) + 7)
  ∧ ¬ (9 * 11 ∣ 4 * ((9 - 1)! + 1) + 9)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesClementDead
