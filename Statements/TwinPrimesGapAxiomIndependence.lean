import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# TwinPrimesGapAxiomIndependence — the recorded gap-sequence facts decide nothing

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The route this eliminates

Problem 9's graph now records several unconditional facts about the prime gap sequence
`gap n = p_{n+1} − p_n`, and they are all facts about the *sequence*: it is strictly
increasing (`TwinPrimesGapParity`), it begins `2, 3`, every gap from index `1` on is even
and at least `2` (`TwinPrimesGapParity`), its `ℕ∞`-valued `liminf` is well defined and at
least `2` (`TwinPrimesH1ENat`), that `liminf` is attained infinitely often and is even
whenever it is finite (`TwinPrimesH1Live`, `TwinPrimesH1Attained`), and Polymath8b's ceiling
puts it at `246` or below.

The route eliminated here is: **derive the twin prime conjecture from those facts.**  Not
"from sieve theory", not "from congruence data" — from the recorded structural properties of
the gap sequence themselves, in any combination, by any argument.  The elimination is a
theorem about the nonexistence of such a derivation, and its certificate is an explicit
sequence.

Write `Rec a` for the conjunction of exactly those recorded properties, read as a predicate
on an arbitrary sequence `a : ℕ → ℕ`.  Then:

* **`Rec` does not entail the twin conclusion.**  `¬ ∀ a, Rec a → ∃ᶠ n, a (n+1) − a n = 2`.
  The witness is `A n = 4n − 1` for `n ≥ 1`, with `A 0 = 2`: it is strictly increasing, it
  begins `2, 3`, every gap from index `1` is exactly `4` — even, at least `2` — its `liminf`
  is `4`, comfortably under `246`, and it has **no gap equal to `2` anywhere at all**, not
  merely finitely often.  Every recorded fact holds of it; the conclusion fails of it.
* **`Rec` does not entail the negation either.**  The witness is `B n = 2n + 1` for `n ≥ 1`,
  with `B 0 = 2`: same properties, `liminf` exactly `2`, and every gap from index `1` is `2`.

So the recorded facts are *independent* of the conjecture: they are consistent with `H₁ = 2`
and consistent with `H₁ = 4`.  Any proof of the twin prime conjecture must use arithmetic
input specific to primality — that some `a (n+1) − a n` is `2` because of what primes *are*,
not because of how the gap sequence is shaped.  That is the residual, and the residual is
this problem's root statement, unchanged.

## Why this is not a shrug: two controls

An elimination is worthless if the eliminated hypothesis set is empty or inert, so both are
checked here rather than asserted.

* **`Rec` is not vacuous.**  Two explicit sequences satisfy it, and their properties are
  computed, not assumed: `A`'s gaps are `4` from index `1` and `B`'s are `2`, and the two
  `liminf` values are pinned to `4` and `2` exactly.
* **`Rec` is not inert.**  It *forces* things: for every `a` satisfying it, a finite `liminf`
  of its gap sequence is even and at least `2`; and consequently no sequence satisfying `Rec`
  has gap-liminf `3`.  If `Rec` implied nothing, that conjunct would be unprovable — it is
  the check that would have failed had the hypothesis set been degenerate, and it is what
  distinguishes "these axioms are too weak" from "these axioms say nothing".

The two controls point opposite ways on purpose.  The first two conjuncts say `Rec` is too
weak to decide the conjecture; the last two say `Rec` is nonetheless strong enough to decide
other things.  A statement carrying only the first pair could be satisfied by a
contradictory `Rec`; one carrying only the second could be satisfied by a `Rec` nobody can
instantiate.

## What is NOT claimed

Nothing about the primes themselves.  `A` and `B` are not prime enumerations and are not
claimed to be — `A 2 = 7` but `A 3 = 11` skips `9`… and skips nothing relevant, because the
point is precisely that `Rec` cannot tell them from the truth.  No bound on `H₁`, upper or
lower, is proved or assumed; `H₁ ≤ 246` appears only inside `Rec`, as a hypothesis about an
arbitrary sequence, and Polymath8b is not invoked.  The twin prime conjecture is neither
proved nor refuted nor made more or less likely, and the answer space of this problem does
not move.  In particular this is **not** an independence result in the logical sense: it says
nothing about Peano arithmetic or ZFC, only that one specific finite list of already-proved
lemmas does not, by itself, entail the conjecture.
-/

namespace Statements.TwinPrimesGapAxiomIndependence

/-- A pseudo-enumeration whose gaps are `1, 4, 4, 4, …`. -/
def A (n : ℕ) : ℕ := if n = 0 then 2 else 4 * n - 1

/-- A pseudo-enumeration whose gaps are `1, 2, 2, 2, …`. -/
def B (n : ℕ) : ℕ := if n = 0 then 2 else 2 * n + 1

/-- Everything problem 9's graph has proved about the prime gap sequence, read as a
predicate on an arbitrary sequence: strictly increasing, starting `2, 3`, every gap from
index `1` on even and at least `2`, and gap-liminf at most the recorded ceiling `246`. -/
def Rec (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ a 0 = 2 ∧ a 1 = 3
  ∧ (∀ n : ℕ, 1 ≤ n → 2 ≤ a (n + 1) - a n ∧ Even (a (n + 1) - a n))
  ∧ Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop ≤ 246

/-- The canonical proposition.  `Rec` does not entail that a gap of `2` occurs infinitely
often, witnessed by `A`, whose gap-liminf is `4` and which has no gap equal to `2` at all;
`Rec` does not entail the negation either, witnessed by `B`, whose gap-liminf is `2`; and
`Rec` is nonetheless not inert — it forces a finite gap-liminf to be even and at least `2`,
hence never `3`. -/
abbrev statement : Prop :=
  (¬ ∀ a : ℕ → ℕ, Rec a → ∃ᶠ n in Filter.atTop, a (n + 1) - a n = 2)
  ∧ (Rec A ∧ Filter.liminf (fun n => ((A (n + 1) - A n : ℕ) : ℕ∞)) Filter.atTop = 4
      ∧ ∀ n : ℕ, 1 ≤ n → A (n + 1) - A n ≠ 2)
  ∧ (Rec B ∧ Filter.liminf (fun n => ((B (n + 1) - B n : ℕ) : ℕ∞)) Filter.atTop = 2
      ∧ ∀ n : ℕ, 1 ≤ n → B (n + 1) - B n = 2)
  ∧ (∀ a : ℕ → ℕ, Rec a → ∀ m : ℕ,
      Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop = (m : ℕ∞) →
      2 ≤ m ∧ Even m)
  ∧ (∀ a : ℕ → ℕ, Rec a →
      Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop ≠ 3)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesGapAxiomIndependence
