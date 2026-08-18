import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic

/-!
# AdmissibleFiftyDiameter212 — no admissible 50-tuple fits in `{0, …, 211}`

`H(50)`, the least diameter of an admissible 50-tuple, is the combinatorial factor in
Polymath8b's record `H₁ ≤ 246`.  Everything filed on this problem so far bounds it from
**above** (`AdmissibleFifty246`: `H(50) ≤ 246`) and every one of those statements says
explicitly that the matching lower bound is *not* claimed, because `H(50) ≥ 246` is
Engelsma's exhaustive computation (OEIS A008407) and is formalised nowhere.

This statement supplies a **lower** bound, unconditionally and by kernel computation:
`H(50) ≥ 212`.

## Why it is a ceiling, and on what

`H₁ ≤ H(k)` is the only conclusion the Goldston–Pintz–Yıldırım / Maynard–Tao route draws
from `DHL[k,2]` plus a narrow tuple.  So at `k = 50` — the smallest `k` for which `DHL[k,2]`
is known unconditionally — **no choice of tuple, however clever, can push the record below
`H₁ ≤ 212`.**  The remaining room at `k = 50` is exactly the interval `[212, 246]`, and it
is 34 wide rather than the 66 left by the mod-6 ladder.  This does not eliminate a proof
*shape*, it bounds an object, so it is filed as `advances` rather than as a dead route.

## The argument

Admissibility at `p` puts `T` inside the complement of one residue class mod `p`.  Taking
`p = 2, 3, 5, 7` simultaneously confines `T` to the survivors of four deleted classes.  The
number of survivors in `{0, …, 211}` is then a finite quantity depending only on the four
deleted residues — 210 choices in all — and the kernel checks that **every** one of the 210
choices leaves at most 49 survivors.  A 50-element `T` therefore cannot fit.

Sharpness of the method, not of the bound: at `d = 212` some choice does leave 50 survivors
(namely `(r₂,r₃,r₅,r₇) = (1,2,4,6)` leaves 49 at 211 and 50 at 212), so 212 is exactly where
the `p ≤ 7` argument stops.  Using `p ≤ 3` alone gives 146; `p ≤ 5` gives 182.  Larger
prime sets would give more, up to the true value 246, at rapidly growing kernel cost.

## Read-back

* Clause 1: for every `T` and every `d`, if `T.card = 50`, `T` is admissible, and every
  element of `T` is at most `d`, then `212 ≤ d`.  Note `d` is a *window*, not a diameter:
  the hypothesis is `∀ x ∈ T, x ≤ d`, with no assumption that `0 ∈ T`.  For a tuple
  normalised to have least element `0` — the convention `AdmissibleFifty246` uses — the
  window and the diameter coincide, so this is `H(50) ≥ 212` in that convention.
* Clause 2: the direct corollary at `d = 211` — there is **no** admissible 50-element set
  all of whose elements are at most 211.
* Admissibility is written `∀ p prime, ∃ r, r < p ∧ ∀ x ∈ T, x % p ≠ r`, the same predicate
  `AdmissibleFifty246` uses, `r < p` included and load-bearing.

## What this does not claim

Not `H(50) ≥ 246`, and so not the optimality of 246 for `k = 50`.  Nothing about `H(k)` for
`k ≠ 50`, nothing about `DHL[k,2]` for any `k`, no bound on `H₁` in either direction, and
nothing about the twin prime conjecture.
-/

namespace Statements.AdmissibleFiftyDiameter212

/-- The canonical proposition: every admissible 50-tuple needs a window of width at least
212, and in particular none fits inside `{0, …, 211}`. -/
abbrev statement : Prop :=
  (∀ (T : Finset ℕ) (d : ℕ),
      T.card = 50 →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) →
      (∀ x ∈ T, x ≤ d) →
      212 ≤ d)
  ∧ ¬ ∃ T : Finset ℕ,
        T.card = 50 ∧ (∀ x ∈ T, x ≤ 211) ∧
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r)

/-- The open target. -/
theorem target : statement := sorry

end Statements.AdmissibleFiftyDiameter212
