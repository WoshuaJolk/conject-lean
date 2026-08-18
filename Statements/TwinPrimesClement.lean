import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Prime.Basic

/-!
# TwinPrimesClement — Clement's congruence criterion for twin primes

P. A. Clement, *Congruences for sets of primes*, Amer. Math. Monthly **56** (1949) 23–25:

> For `n ≥ 2`, the pair `(n, n + 2)` is a twin prime pair **iff**
> `4((n − 1)! + 1) + n ≡ 0 (mod n(n + 2))`.

The statement below records the criterion for odd `n ≥ 3`, which is where all of the content
lies — the only even `n` with `n` prime is `n = 2`, and `(2, 4)` is not a twin pair — and
then pins it to the problem's root: the twin prime conjecture is equivalent to the assertion
that the single divisibility `n(n+2) ∣ 4((n−1)! + 1) + n` holds for arbitrarily large odd
`n`.

## Why this is worth recording

It converts an existential statement about two simultaneous primalities into **one**
divisibility condition on **one** integer.  It is unconditional and elementary: two
applications of Wilson's theorem, which Mathlib has as
`Nat.prime_iff_fac_equiv_neg_one`, plus the observation `(n+2)(n+1) ≡ 2 (mod n+3)` that
turns `(n+1)!` into `2·(n−1)!` modulo `n + 2`.

It is also, read the other way, a barrier: the criterion is an *equivalence*, so it
transfers no information.  Any attempt to settle the conjecture by exhibiting structure in
the congruence is attacking a restatement, and the restatement's difficulty is exactly the
original's.  Clement said as much in 1949; this records it in a form a machine can check.

Mathlib has neither Clement's criterion nor any twin-prime-specific factorial congruence, and
no formalisation of it was found in Mathlib, the Archive of Formal Proofs, or the Coq
libraries.
-/

namespace Statements.TwinPrimesClement

/-- Clement's criterion, and its consequence that the twin prime conjecture is equivalent to
a single factorial congruence holding for arbitrarily large odd `n`. -/
abbrev statement : Prop :=
  (∀ n : ℕ, 3 ≤ n → Odd n →
      ((Nat.Prime n ∧ Nat.Prime (n + 2)) ↔
        n * (n + 2) ∣ 4 * (Nat.factorial (n - 1) + 1) + n))
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
      ↔ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ 3 ≤ n ∧ Odd n ∧
            n * (n + 2) ∣ 4 * (Nat.factorial (n - 1) + 1) + n))

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesClement
