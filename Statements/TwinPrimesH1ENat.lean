import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# TwinPrimesH1ENat — `H₁` defined honestly, in `ℕ∞`, and pinned to the root

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The problem this statement solves

Problem 9 tracks `H₁ := liminf_{n → ∞} (p_{n+1} − p_n)`, and its root statement is
deliberately *not* `H₁ = 2`.  The reason, recorded when the problem was posed: Mathlib's
`liminf` over `ℕ` is `sSup {a | ∀ᶠ n, a ≤ u n}`, and `sSup` of an unbounded set of naturals
is `0` by junk convention.  So an `ℕ`-valued `H₁` denotes what a reader expects only given
that the gap sequence has bounded liminf — Zhang's theorem, sharpened by Polymath8b, and
formalised nowhere.  A Lean proposition mentioning an `ℕ`-valued `H₁` would carry that
unformalised dependency silently inside itself.

The fix is to widen the codomain rather than to assume the theorem.  `ℕ∞ = WithTop ℕ` is a
complete lattice, so `sSup` there is the honest supremum, no boundedness hypothesis needed:
if the gaps did tend to infinity the liminf would be `⊤`, which is the true answer, not `0`.
`H₁` defined in `ℕ∞` is therefore faithful **unconditionally**, and everything below is
proved with no sieve input of any kind.

The last conjunct makes that contrast a checked fact rather than a claim about Lean: for the
sequence `u n = n`, the `ℕ`-valued liminf is `0` and the `ℕ∞`-valued liminf is `⊤`.  Same
sequence, same filter, two conventions, and only one of them is the mathematics.

## Read-back, term by term

* `gap n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n`, on Mathlib's **0-indexed**
  enumeration (`Nat.nth Nat.Prime 0 = 2`).  Truncated natural subtraction is harmless here
  because the enumeration is strictly increasing.  That `gap` is the prime gap sequence and
  not something displaced by one is pinned by the first conjunct: `gap 0 = 1` (`3 − 2`),
  `gap 1 = 2` (`5 − 3`), `gap 2 = 2` (`7 − 5`), `gap 3 = 4` (`11 − 7`).
* `H₁ = liminf (fun n => (gap n : ℕ∞)) atTop`, the cast being into `ℕ∞`.
* `2 ≤ H₁`, unconditionally.  This is the elementary lower bound: past the first gap every
  gap is even and positive.  It is the `ℕ∞` form of what `TwinPrimesGapParity` proves about
  the sequence.
* `H₁ = 2 ↔ (∀ N, ∃ p, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))` — an **equivalence with the
  root statement of this problem, verbatim**.  Both directions are proved.

  Left to right: if `H₁ = 2` then `3` is not in the set the `sSup` is taken over, so the gap
  is `< 3` — hence exactly `2` — infinitely often, and each such place is a twin pair beyond
  any prescribed bound.

  Right to left: a twin pair `(p, p + 2)` with `p > 2` is a pair of *consecutive* primes,
  because `p + 1` is even and larger than `2`; so it realises `gap (count Nat.Prime p) = 2`,
  and twin pairs beyond every bound give indices beyond every bound.  That forces
  `H₁ ≤ 2`, and with `2 ≤ H₁` gives equality.

## What this does and does not do

It does **not** prove or disprove anything open.  It is a bridge: it says that the number
the progress space tracks is a well-defined element of `ℕ∞` with no hidden dependency, that
its floor is `2`, and that the conjecture is *exactly* the assertion that the floor is
attained.  Anyone who later formalises `H₁ ≤ 246` can now state it against this `H₁`; and
`H₁ ≤ 246` would additionally give `H₁ ≠ ⊤`, which is precisely the input this construction
was designed not to need.
-/

namespace Statements.TwinPrimesH1ENat

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`: `gap 0 = 3 - 2 = 1`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁`, the least gap between consecutive primes attained infinitely often, as an element
of `ℕ∞`.  The codomain is `ℕ∞` and not `ℕ` so that the `sSup` inside `liminf` is the honest
supremum: no boundedness of the gap sequence is assumed anywhere. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The canonical proposition: the gap sequence starts `1, 2, 2, 4`; `H₁ ≥ 2`
unconditionally; `H₁ = 2` is equivalent to the twin prime conjecture in the exact form this
problem's root statement takes; and the convention that forced the move to `ℕ∞` is exhibited
on the sequence `u n = n`, whose liminf is `0` in `ℕ` and `⊤` in `ℕ∞`. -/
abbrev statement : Prop :=
  (gap 0 = 1 ∧ gap 1 = 2 ∧ gap 2 = 2 ∧ gap 3 = 4)
  ∧ 2 ≤ H1
  ∧ (H1 = 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
  ∧ (Filter.liminf (fun n : ℕ => n) Filter.atTop = 0
      ∧ Filter.liminf (fun n : ℕ => (n : ℕ∞)) Filter.atTop = ⊤)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesH1ENat
