import Mathlib.Algebra.Group.Nat.Even
import Commons.Basic

/-!
# S001 — the product of two consecutive naturals is even

This module is the **single source of truth** for what S001 means. The verifier reads
`Statements.S001.statement` and nothing else; a submission never gets to supply its own
copy of the statement.

Submissions **must not** import this module (the verifier rejects them if they do),
because `target` below is closed with `sorry`.
-/

namespace Statements.S001

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop := ∀ n : ℕ, Even (n * (n + 1))

/-- The open target. Replacing this `sorry` is not how the problem is solved: a
submission proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.S001
