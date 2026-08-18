import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# TwinPrimesCountingBridge — the counting form is exactly the root statement

Pins `TwinPrimesCountingResidual` to the problem's root.  Without this the residual would be
a plausible-looking reformulation resting on nobody's proof; with it, the residual is the
root, machine-checked, and a contributor may attack whichever side is convenient.

Neither direction assumes anything unproved.  Left to right: if some `M` twin lower members
exist for every `M`, take `M = N + 2`; the resulting set cannot sit inside `Finset.range
(N+1)`, which has only `N+1` elements, so it contains a twin lower member exceeding `N`.
Right to left: induct on `M`, extending a set of `M` twin lower members by a twin lower
member larger than its `Finset.sup`, which is therefore not already in it.
-/

namespace Statements.TwinPrimesCountingBridge

/-- The counting form of the twin prime conjecture is equivalent to the unbounded form used
as the root of this problem. -/
abbrev statement : Prop :=
  (∀ M : ℕ, ∃ T : Finset ℕ, M ≤ T.card ∧ ∀ p ∈ T, Nat.Prime p ∧ Nat.Prime (p + 2))
    ↔ (∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesCountingBridge
