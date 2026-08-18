import Mathlib.Data.Nat.Prime.Basic

/-!
# TwinPrimesSundaram — the twin prime conjecture as a covering problem for four bilinear forms

## The reformulation

For `k ≥ 1`, the pair `(6k − 1, 6k + 1)` consists of two primes **exactly** when `k` is not
represented by any of the four bilinear forms

`6ab + a + b`,  `6ab − a − b`,  `6ab + a − b`,  `6ab − a + b`  (`a, b ≥ 1`).

Every twin prime pair beyond `(3,5)` has this shape, so the twin prime conjecture is
equivalent to: **the four forms above do not cover all sufficiently large integers.**

This is the twin-prime analogue of the sieve of Sundaram, which does the same job for a
single prime with the forms `2ab + a + b`.  Below it is stated with additive equations
(`k + a + b = 6ab` rather than `k = 6ab − a − b`) so that no truncated natural subtraction
appears anywhere in the proposition.

## Why this is worth having

It replaces two simultaneous primality conditions — an intrinsically multiplicative,
unbounded search — by a single **non-representability** condition for an explicit family of
bilinear forms.  The twin prime conjecture becomes a covering question about the image of
`(a,b) ↦ 6ab ± a ± b`, a set of the same flavour as the ones studied in the multiplication
table problem, where the density of `{ab : a,b ≤ n}` is understood.  That is a different
literature from sieve theory, and the point of recording the bridge in machine-checked form
is to let anyone attack this problem from that side without first re-deriving the
correspondence.

Read the other way it is a barrier of the same kind as Clement's criterion: the statement is
an equivalence, so it transfers no information on its own, and any attack on the
non-representability side inherits exactly the difficulty of the original.

## Mechanism

`6k ± 1` is coprime to `6`, so every divisor is `≡ 1` or `≡ 5 (mod 6)`.  A factorisation of
`6k + 1` has both factors in the same class, giving `(6a+1)(6b+1)` or `(6a−1)(6b−1)`, i.e.
`k = 6ab + a + b` or `k = 6ab − a − b`.  A factorisation of `6k − 1` has one factor in each
class, giving `(6a+1)(6b−1)` or `(6a−1)(6b+1)`, i.e. `k = 6ab − a + b` or `k = 6ab + a − b`.
Conversely each representation exhibits a factorisation with both factors exceeding `1`.
-/

namespace Statements.TwinPrimesSundaram

/-- Clause (i) is the Sundaram-type criterion; clause (ii) turns the problem's root statement
into the assertion that four bilinear forms fail to cover the integers. -/
abbrev statement : Prop :=
  (∀ k : ℕ, 0 < k →
      ((Nat.Prime (6*k - 1) ∧ Nat.Prime (6*k + 1)) ↔
        ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
            (k = 6*a*b + a + b ∨ k + a + b = 6*a*b ∨
             k + b = 6*a*b + a ∨ k + a = 6*a*b + b)))
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
      ↔ (∀ N : ℕ, ∃ k : ℕ, N < k ∧ 0 < k ∧
            ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
                (k = 6*a*b + a + b ∨ k + a + b = 6*a*b ∨
                 k + b = 6*a*b + a ∨ k + a = 6*a*b + b)))

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesSundaram
