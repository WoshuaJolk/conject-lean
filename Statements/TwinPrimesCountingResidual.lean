import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# TwinPrimesCountingResidual — the quantitative form of the twin prime conjecture

This is the **residual** of `TwinPrimesDirichletBarrier`: the statement that survives when
Dirichlet-level distributional information about the primes is cut away.

The barrier exhibits a set `S` — the primes `p` with `p + 2` composite — which is an infinite
set of primes, unbounded in every reduced residue class modulo every modulus, and which
contains no twin pair at all.  Every *qualitative* property of the primes of that kind is
therefore useless: `S` has it too.  The primes and `S` differ in exactly one respect, namely
the twin-prime lower members themselves, so the only inputs that can separate them are
inputs that *count* twin pairs.

The statement below is that counting form: for every `M` there is a set of `M` twin-prime
lower members.  It is equivalent to the problem's root statement — the companion statement
`TwinPrimesCountingBridge` proves the equivalence in Lean — and it is stated here in the
shape a surviving argument must actually take.  It is open.

Deliberately no counting *function* appears.  A `π₂ : ℕ → ℕ` defined by `Finset.filter`
carries a `DecidablePred` instance in its elaborated term, and a submission restating it
with a different instance would fail the verifier's definitional-equality bridge for a
reason that has nothing to do with mathematics.  `∃ T : Finset ℕ, M ≤ T.card ∧ …` says the
same thing with no instance in the term.
-/

namespace Statements.TwinPrimesCountingResidual

/-- For every `M` there are at least `M` twin-prime lower members: a finite set of `M`
naturals, each of which is prime and has a prime successor-by-two. -/
abbrev statement : Prop :=
  ∀ M : ℕ, ∃ T : Finset ℕ, M ≤ T.card ∧ ∀ p ∈ T, Nat.Prime p ∧ Nat.Prime (p + 2)

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesCountingResidual
