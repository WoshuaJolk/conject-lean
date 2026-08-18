import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# H1BoundedGapBridge — what `H₁ ≤ D` is, and where a sieve input plugs in

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

`H₁` is defined here exactly as in `TwinPrimesH1ENat` — `liminf` of the prime gap sequence,
taken in `ℕ∞` so that the `sSup` inside `liminf` is the honest supremum and no boundedness
of the gaps is assumed.  That statement proves `H₁ = 2 ↔` the twin prime conjecture.  This
one is the **general-`D`** version of that bridge, plus the reduction that a bounded-gaps
theorem actually feeds into.

## What the four working conjuncts say

1. `2 ≤ H₁`, unconditionally.  Restated so this module stands alone.

2. **For every `D`, `H₁ ≤ D` if and only if, beyond every bound, some window of width `D`
   contains two primes.**  Both directions.  Left to right is the non-obvious one: `H₁ ≤ D`
   is a statement about `liminf`, and turning it into an actual pair of primes needs the
   infimum to be attained — which is why `ℕ∞`, a well-ordered complete lattice, is the right
   codomain.  Right to left needs the observation that two primes `p < q` with `q − p ≤ D`
   force a *consecutive* pair of primes inside `[p, q]`, obtained by pushing `p` forward with
   `Nat.count`/`Nat.nth`; without that step "two primes close together" would not bound any
   term of the gap sequence.

3. **The reduction.**  If `T` is any finite set of naturals with every element `≤ D`, and if
   beyond every bound there is an `n` with at least two of `{n + t : t ∈ T}` prime, then
   `H₁ ≤ D`.  This is the shape a Dickson–Hardy–Littlewood input `DHL[k,2]` has.  Instantiated
   at the admissible 50-tuple of diameter 246 proved to exist in `AdmissibleFifty246`, and at
   `D = 246`, it yields `H₁ ≤ 246` — Polymath8b's unconditional record — from `DHL[50,2]` and
   nothing else.  Note that admissibility is **not** a hypothesis here: admissibility is what
   makes the `DHL` premise *true*, and is not needed to make this implication valid.

4. `H₁ ≤ 2 ↔` the twin prime conjecture in the exact form this problem's root statement
   takes.  This is conjunct 2 at `D = 2` combined with conjunct 1, and it is stated
   separately as a read-back: it pins the general-`D` machinery to the problem's root, so a
   `D` displaced by one or a gap sequence displaced by one index would be caught here.

## The fifth conjunct is a vacuity check, and it is the point

Conjunct 3 is an implication whose premise is a theorem nobody has formalised.  A conditional
theorem is worthless if its premise is contradictory, and the premise here cannot be
exhibited in Lean, because *every* instance of it implies bounded prime gaps — Zhang's
theorem, unformalised.  So the check has to be made structurally instead.

Conjunct 5 does that: at `T = {0, 2}` and `D = 2`, the premise of conjunct 3 is proved
**equivalent to the twin prime conjecture itself**, verbatim as the root statement writes it.
So the premise shape is not a contradiction dressed up as a hypothesis; it is the family of
statements of which the conjecture is the tightest member, and conjunct 2 shows the premise
at width `D` holds precisely when `H₁ ≤ D`.

## What this does and does not settle

Nothing open.  No sieve, no Bombieri–Vinogradov, no Selberg weights appear; every conjunct is
proved from `Nat.nth`, `Nat.count` and lattice facts about `ℕ∞`.  What it does is make the
residual exact: after `AdmissibleFifty246` and this statement, a machine-checked `H₁ ≤ 246`
requires `DHL[50,2]` and *nothing else* — no further combinatorics, and no further work
relating windows of primes to the liminf of the gap sequence.
-/

namespace Statements.H1BoundedGapBridge

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`: `gap 0 = 3 - 2 = 1`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁`, the least gap between consecutive primes attained infinitely often, in `ℕ∞`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The canonical proposition.  `H₁ ≥ 2`; `H₁ ≤ D` is equivalent to two primes appearing in
a window of width `D` beyond every bound; a `DHL`-shaped premise for any tuple of diameter
at most `D` gives `H₁ ≤ D`; `H₁ ≤ 2` is the twin prime conjecture; and that `DHL`-shaped
premise, at the tuple `{0, 2}`, is the twin prime conjecture, so it is not vacuous. -/
abbrev statement : Prop :=
  2 ≤ H1
  ∧ (∀ D : ℕ, H1 ≤ (D : ℕ∞) ↔
      ∀ N : ℕ, ∃ n a b : ℕ, N < n ∧ a < b ∧ b ≤ D ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b))
  ∧ (∀ (T : Finset ℕ) (D : ℕ), (∀ x ∈ T, x ≤ D) →
      (∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T, a < b ∧
          Nat.Prime (n + a) ∧ Nat.Prime (n + b)) →
      H1 ≤ (D : ℕ∞))
  ∧ (H1 ≤ 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
  ∧ ((∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ ({0, 2} : Finset ℕ), ∃ b ∈ ({0, 2} : Finset ℕ),
        a < b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b))
      ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.H1BoundedGapBridge
