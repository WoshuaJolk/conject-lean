import Mathlib.Algebra.Ring.Parity
import Commons.SetPairSystem

namespace Statements.S002

/-- The canonical proposition. This is the type the verifier demands.

Every `(n,n)`-bounded `1`-cross intersecting set pair system has size at most the size of
the Füredi–Gyárfás–Király construction: at most `5 ^ (n/2)` when `n` is even, and at most
`2 * 5 ^ ((n-1)/2)` when `n` is odd. -/
abbrev statement : Prop :=
  ∀ (n m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS n n m A B →
      (Even n → m ≤ 5 ^ (n / 2)) ∧ (Odd n → m ≤ 2 * 5 ^ ((n - 1) / 2))

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.S002

-- Commons.OneCrossSPS, the shared vocabulary this statement is built from:
--   def OneCrossSPS (a b m : ℕ) (A B : Fin m → Finset ℕ) : Prop :=
--     (∀ i, (A i).card ≤ a) ∧ (∀ i, (B i).card ≤ b) ∧
--     (∀ i, A i ∩ B i = ∅) ∧ (∀ i j, i ≠ j → (A i ∩ B j).card = 1)
--
-- The full module, with the term-by-term read-back against the source and the note on the
-- `(n-1)/2` spelling, is Statements/S002.lean in the verifier repo.
