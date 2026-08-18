import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# H1LeFromPrimePairs — arbitrarily large prime pairs of bounded spacing bound `H₁`

`TwinPrimesH1ENat` (proved on this problem) defines
`gap n = Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n` and
`H₁ = liminf (fun n => (gap n : ℕ∞)) atTop`, and its own prose closes with:
*"Anyone who later formalises `H₁ ≤ 246` can now state it against this `H₁`."*
This statement is the missing conversion.  `gap` and `H₁` are repeated here **verbatim**
from `TwinPrimesH1ENat` so that the two statements speak about the same number.

## Why this is the piece that was missing

`AdmissibleFifty246` establishes `H(50) ≤ 246`, the combinatorial half of Polymath8b's
record.  On its own it "moves no bound on `H₁`" — its own scope says so.  The analytic
half, `DHL[50,2]`, is unformalised.  But *even granting `DHL[50,2] `*, nothing on this
problem said how a `DHL` statement plus a narrow admissible tuple produces a bound on the
`ℕ∞`-valued `H₁` that the progress space tracks.  That last step is not analysis: it is
the elementary observation that two primes at distance `≤ d` force a **consecutive** pair
at distance `≤ d`, plus the `liminf` bookkeeping.  It is proved here unconditionally.

Consequence, once `DHL[50,2]` is available: clause 2 applied to the 50-tuple supplied by
`AdmissibleFifty246` gives `H₁ ≤ 246`.  The residual is then exactly one named input.

## Read-back, clause by clause

1. **The kernel.**  If for every `N` there are primes `p, q` with `N < p < q ≤ p + d`,
   then `H₁ ≤ d`.  Note `p < q` and `q ≤ p + d` are separate: no `ℕ`-subtraction appears,
   so nothing can be hidden by truncation.  The hypothesis is about *arbitrarily large*
   pairs (`N < p` for every `N`), which is what a `liminf` bound needs; a single pair, or
   pairs below a bound, would give nothing.
2. **The `DHL`-shaped form.**  For a finite `T` with every element `≤ d`, if for every `N`
   there is `n > N` and two **distinct** `a, b ∈ T` with `n + a` and `n + b` both prime,
   then `H₁ ≤ d`.  This is exactly the shape `DHL[k,2]` delivers when instantiated at an
   admissible `k`-tuple: "at least two of `n + T` are prime, infinitely often".
   `a ≠ b` rather than `a < b`, so the caller need not order them.
3. **Calibration against a known answer.**  Clause 1 at `d = 2` must reproduce the
   already-proved right-to-left direction of `TwinPrimesH1ENat`'s equivalence: the twin
   prime conjecture implies `H₁ ≤ 2`.  It is asserted here so that an off-by-one in
   clauses 1–2 cannot pass unnoticed.

## What this does not do

It proves no bound on `H₁`.  Both clause 1 and clause 2 are implications whose hypotheses
are, at `d = 246`, precisely the unformalised analytic input; at `d = 2` precisely the
conjecture.  It asserts nothing about admissibility, about `DHL[k,2]` for any `k`, and
nothing about `H(50)`.
-/

namespace Statements.H1LeFromPrimePairs

/-- The `n`-th prime gap, 0-indexed.  Verbatim from `Statements.TwinPrimesH1ENat`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁` in `ℕ∞`.  Verbatim from `Statements.TwinPrimesH1ENat`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The canonical proposition. -/
abbrev statement : Prop :=
  (∀ d : ℕ,
      (∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ q ≤ p + d ∧ Nat.Prime p ∧ Nat.Prime q) →
      H1 ≤ (d : ℕ∞))
  ∧ (∀ (T : Finset ℕ) (d : ℕ),
      (∀ x ∈ T, x ≤ d) →
      (∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
          a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)) →
      H1 ≤ (d : ℕ∞))
  ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) → H1 ≤ 2)

/-- The open target. -/
theorem target : statement := sorry

end Statements.H1LeFromPrimePairs
