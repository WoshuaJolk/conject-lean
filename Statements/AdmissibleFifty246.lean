import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# AdmissibleFifty246 — `H(50) ≤ 246`: a narrow admissible 50-tuple exists

A finite set `T ⊆ ℕ` is **admissible** when, for every prime `p`, some residue class mod `p`
contains no element of `T`.  Admissibility is exactly the condition that no fixed prime
obstructs `{n + t : t ∈ T}` from consisting entirely of primes infinitely often, and it is
the combinatorial input to every bounded-gaps result in the Goldston–Pintz–Yıldırım /
Zhang / Maynard–Tao line: if `DHL[k,2]` holds for admissible `k`-tuples, then
`H₁ ≤ H(k)`, where `H(k)` is the least diameter of an admissible `k`-tuple.

Polymath8b's unconditional record `H₁ ≤ 246` is exactly `DHL[50,2]` combined with
`H(50) ≤ 246`.  This statement is the second factor, and it is the only factor of that
record which is a finite, kernel-checkable assertion: `DHL[50,2]` rests on
Bombieri–Vinogradov, which is not formalised anywhere.

## Read-back, term by term

* `T.card = 50` — a 50-tuple, with 50 *distinct* elements.
* `0 ∈ T ∧ 246 ∈ T ∧ ∀ x ∈ T, x ≤ 246` — the diameter `max T - min T` is **exactly** 246.
  The endpoints are asserted to be attained, so this is not merely "contained in an
  interval of length 246"; and no `ℕ`-subtraction appears, so no truncation can hide here.
* `∀ p, p.Prime → ∃ r, r < p ∧ ∀ x ∈ T, x % p ≠ r` — admissibility.  **The bound `r < p` is
  load-bearing.**  Without it the clause is vacuously true, since `r := p` is never a value
  of `x % p`; with it, `r` names a genuine residue class mod `p` and the clause says that
  class is empty of elements of `T`.

There are no hypotheses, so a vacuous-hypothesis proof is structurally unavailable.  The
proposition is a bare existential: proving it requires exhibiting the tuple.

## What this does and does not settle

It does not settle the twin prime conjecture, and it moves no bound on `H₁`: `H₁ ≤ 246`
needs the analytic half as well.  What it does is discharge, once and for all and by
kernel computation, the combinatorial half of the current record, and pin the residual to
a single named unformalised input.

`H(50) = 246` exactly — the matching lower bound is Engelsma's exhaustive computation
(OEIS A008407, a(50) = 246), which is *not* claimed here.  Only `H(50) ≤ 246` is claimed.
-/

namespace Statements.AdmissibleFifty246

/-- The canonical proposition.  There exists an admissible 50-tuple of diameter exactly
246: a 50-element set of naturals with least element 0 and greatest element 246 which, for
every prime `p`, omits some residue class `r < p` modulo `p`. -/
abbrev statement : Prop :=
  ∃ T : Finset ℕ,
    T.card = 50 ∧
    0 ∈ T ∧ 246 ∈ T ∧ (∀ x ∈ T, x ≤ 246) ∧
    (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r)

/-- The open target. -/
theorem target : statement := sorry

end Statements.AdmissibleFifty246
