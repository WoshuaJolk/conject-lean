import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# AdmissibleTupleFloorSix — the narrow-tuple route has a hard floor at 6, and it is a theorem

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The route this eliminates

Every unconditional bound on `H₁` since Goldston–Pintz–Yıldırım has the same two-part shape:
an analytic input `DHL[k,2]` — for every admissible `k`-tuple `T`, there are infinitely many
`n` with at least two of `{n + t : t ∈ T}` prime — combined with a **narrow admissible
`k`-tuple**, giving `H₁ ≤ diam T`.  Zhang used `k = 3500000`, Maynard `k = 105`, Polymath8b
`k = 50` with `diam = 246`.  Substantial effort has gone into the second half: finding
`k`-tuples of the least possible diameter, for which `H(k)` is tabulated (OEIS A008407).

That second half cannot deliver anything below 6.  This statement proves it.

## What is proved

**Three integers inside a window of width 5 always meet every residue class modulo 2 or
every residue class modulo 3.**  In six consecutive integers each class mod 6 occurs exactly
once; admissibility at 2 removes three of the six classes, and among the three survivors —
`c`, `c + 2`, `c + 4` mod 6 — the residues mod 3 are pairwise distinct, so admissibility at 3
removes exactly one more.  Two classes remain, so an admissible tuple in such a window has at
most two elements.  Hence:

* `H(k) ≥ 6` for every `k ≥ 3` — an admissible tuple with three or more elements, contained
  in `[lo, lo + d]`, forces `d ≥ 6`; and
* the floor is **attained**: `{0, 2, 6}` is admissible, has three elements and diameter 6.

So `H(3) = 6`, and the narrow-tuple half of the route is *already optimal at k = 3*: no
search over tuples, however large, can produce a bound below 6.

## Why the residual is the root statement itself

The only escape is `k = 2`.  But `DHL[2,2]` at the admissible pair `{0, 2}` says exactly that
there are infinitely many `n` with `n` and `n + 2` both prime — this problem's root statement,
verbatim.  So within this route, every bound strictly below 6 requires an input that already
*is* the twin prime conjecture (indeed `DHL[2,2]` gives de Polignac for every even gap).  The
route therefore stops at 6, and what survives is the root.

`{0, 2}` is exhibited here as admissible, so `k = 2` is not eliminated for lack of a tuple;
it is eliminated as a *route*, because its analytic input is the conclusion.

## Relation to the parity barrier, stated carefully

The problem's progress record carries a ceiling from 2 to 6 attributed to the parity barrier,
flagged — correctly — as heuristic: Polymath8b §8 is informal and conditional on the Möbius
randomness law, and it is a statement about *sieve methods*.  The present statement is
logically independent of it and is a **theorem**: it is about the *combinatorics of tuples*,
not about sieves, and it needs no unproved input.  That the two reach the same number, 6,
from opposite halves of the same route is worth recording, but this statement neither proves
nor assumes the parity barrier.

## What is NOT claimed

Not claimed: that `H₁ > 4`, or any lower bound on `H₁` beyond the elementary `H₁ ≥ 2`; that
no method whatsoever can reach `H₁ ≤ 4` — variants with `m ≥ 3`, non-tuple methods and
methods not of the `DHL[k,2] + tuple` shape are entirely outside this scope; `DHL[k,2]` for
any `k`; and the exact values `H(k)` for `k ≥ 4`.  The answer space of the problem does not
move: this is a fact about a method, and a ceiling is never subtracted.

## The last conjunct is the control

`{0, 2, 4}` is proved **not** admissible.  Without it the admissibility predicate could be
satisfied by everything and every conjunct above would be true for a void reason; with it,
admissibility is shown to be a constraint that actually rejects a set of the same size and
smaller diameter than `{0, 2, 6}`.  Conjuncts three and four likewise witness that the
hypotheses of conjuncts one and two are satisfiable, and conjunct three witnesses them at the
boundary `d = 6`, so the bound is sharp rather than merely true.
-/

namespace Statements.AdmissibleTupleFloorSix

/-- The canonical proposition.  An admissible tuple inside a window of width 5 has at most
two elements; hence any admissible tuple with at least three elements has diameter at least
6; `{0, 2, 6}` attains 6; `{0, 2}` is admissible; and `{0, 2, 4}` is not. -/
abbrev statement : Prop :=
  (∀ (T : Finset ℕ) (lo : ℕ), (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + 5) →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) → T.card ≤ 2)
  ∧ (∀ (T : Finset ℕ) (lo d : ℕ), (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) → 3 ≤ T.card →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) → 6 ≤ d)
  ∧ (({0, 2, 6} : Finset ℕ).card = 3 ∧
      ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6} : Finset ℕ), x % p ≠ r)
  ∧ (({0, 2} : Finset ℕ).card = 2 ∧
      ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2} : Finset ℕ), x % p ≠ r)
  ∧ ¬ (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 4} : Finset ℕ), x % p ≠ r)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.AdmissibleTupleFloorSix
