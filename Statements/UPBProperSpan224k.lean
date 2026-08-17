import Mathlib.Data.Nat.Basic

/-!
# UPBProperSpan224k — why the root statement may omit the properness clause

A UPB is normally required to span a *proper* subspace, and the canonical statement of
problem `MinUPB224kMinus1` does not say so. It does not have to, and this is the arithmetic
that discharges the obligation.

The `4k+2` states are nonzero and pairwise orthogonal, hence linearly independent, so their
span has dimension exactly `4k+2`. The ambient space `C² ⊗ C² ⊗ C^(4k−1)` has dimension
`2 · 2 · (4k−1) = 16k − 4`. So the span is proper exactly when `4k+2 < 16k−4`, i.e. `6 < 12k`,
which holds for every `k ≥ 1` and in particular under the root's `2 ≤ k` guard.

Filed so that the omission in `MinUPB224kMinus1` is checkable rather than asserted.
-/

namespace Statements.UPBProperSpan224k

/-- The canonical proposition. For every `k ≥ 2` the cardinality `4k+2` demanded by
`MinUPB224kMinus1` is strictly below `dim (C² ⊗ C² ⊗ C^(4k−1)) = 2 · 2 · (4k−1)`, so a
pairwise-orthogonal family of that size necessarily spans a proper subspace. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k → 4 * k + 2 < 2 * 2 * (4 * k - 1)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UPBProperSpan224k
