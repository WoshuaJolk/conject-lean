import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# DHL50ImpliesH1Le246 — the record `H₁ ≤ 246` reduced to exactly one named input

Polymath8b's unconditional record is `H₁ ≤ 246`, and it is the product of two factors:

* `DHL[50,2]` — *analytic.*  For every admissible 50-tuple `T`, there are infinitely many
  `n` for which at least two of `{n + t : t ∈ T}` are prime.  Rests on Bombieri–Vinogradov
  and the Maynard–Tao sieve; **formalised nowhere.**
* `H(50) ≤ 246` — *combinatorial.*  An admissible 50-tuple of diameter 246 exists.  Finite,
  and kernel-checkable (`AdmissibleFifty246`).

Nothing on this problem previously connected those two factors to the `ℕ∞`-valued `H₁` the
progress space actually tracks.  This statement is that connection, proved unconditionally:
**`DHL[50,2]` alone implies `H₁ ≤ 246`.**  The tuple and the passage from "two primes at
distance ≤ 246, infinitely often" to a `liminf` bound on *consecutive* prime gaps are both
discharged inside the proof, so after this the residual on the record is one named
hypothesis and nothing else.

`gap` and `H₁` are repeated **verbatim** from `Statements.TwinPrimesH1ENat`, which is proved
on this problem, so the bound lands on the same number that statement pins to the root.

## Read-back, clause by clause

1. **The reduction, with `DHL[50,2]` as normally stated.**  The hypothesis quantifies over
   *every* admissible 50-tuple — that is `DHL[50,2]` verbatim — and the conclusion is
   `H₁ ≤ 246`.  Admissibility is written `∀ p prime, ∃ r < p, ∀ x ∈ T, x % p ≠ r`; the
   bound `r < p` is load-bearing, since `r := p` would satisfy the rest vacuously.
2. **The same reduction with the analytic input demanded at one tuple only.**  There is an
   explicit `T` with `T.card = 50`, `0 ∈ T`, `246 ∈ T`, `∀ x ∈ T, x ≤ 246` (so the diameter
   is exactly 246, endpoints attained, no `ℕ`-subtraction anywhere) and `T` admissible, such
   that `DHL` *at that single `T`* already yields `H₁ ≤ 246`.  This is the strong form:
   clause 1 follows from it, and it names precisely how little of `DHL[50,2]` is needed.

## What this does not do

It proves no bound on `H₁`.  Both clauses are implications, and their hypotheses are exactly
the unformalised analytic input.  It claims nothing about `H(50) ≥ 246` (Engelsma's
exhaustive computation, OEIS A008407), nothing about `DHL[k,2]` for any `k`, and nothing
about the twin prime conjecture, which is `H₁ = 2` and is not reachable this way: the parity
barrier recorded on this problem blocks every method of this shape below 6.
-/

namespace Statements.DHL50ImpliesH1Le246

/-- The `n`-th prime gap, 0-indexed.  Verbatim from `Statements.TwinPrimesH1ENat`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁` in `ℕ∞`.  Verbatim from `Statements.TwinPrimesH1ENat`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ((∀ T : Finset ℕ, T.card = 50 →
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) →
        ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
          a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b))
      → H1 ≤ 246)
  ∧ (∃ T : Finset ℕ,
        T.card = 50 ∧ 0 ∈ T ∧ 246 ∈ T ∧ (∀ x ∈ T, x ≤ 246) ∧
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) ∧
        ((∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
            a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)) → H1 ≤ 246))

/-- The open target. -/
theorem target : statement := sorry

end Statements.DHL50ImpliesH1Le246
