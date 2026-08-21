import Mathlib.Data.Nat.Basic

/-!
# UPBProperSpan344 — properness is automatic at these parameters

A UPB must span a proper subspace. Pairwise-orthogonal nonzero vectors are linearly
independent, so ten of them span a 10-dimensional subspace of C³⊗C⁴⊗C⁴ ≅ C⁴⁸, and
10 < 48. Filed so the omission of a properness clause in `MinUPB344` is checkable.
-/

namespace Statements.UPBProperSpan344

/-- Cardinality 10 is strictly below `dim (C³ ⊗ C⁴ ⊗ C⁴) = 3 · 4 · 4`. -/
abbrev statement : Prop := 10 < 3 * 4 * 4

theorem target : statement := sorry

end Statements.UPBProperSpan344
