import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Ring.Nat
import Commons.SetPairSystem

/-!
# BlockProductOptimum — the exact optimum of the block-product functional

A *block profile* is a finite list of pairs `(u_i, v_i)` of naturals.  It contributes
`∏ (u_i * v_i + 1)` to the size of a product construction and `∑ u_i`, `∑ v_i` to the two
card budgets.  This statement says the profile functional never exceeds the
Füredi–Gyárfás–Király value: with both budgets at most `n`,

  `∏ (u_i v_i + 1) ≤ 5 ^ (n/2)`        when `n` is even, and
  `∏ (u_i v_i + 1) ≤ 2 * 5 ^ ((n-1)/2)` when `n` is odd,

with equality realised by `n/2` copies of the pentagon block `(2,2)` (plus one `(1,1)` block
when `n` is odd).  The odd branch is spelled `2 * 5 ^ ((n-1)/2)`, exactly as FGK Corollary 1.2
writes it, and the two parities are two separate implications rather than one `if`.

Both budgets are needed separately: with only `∑ u_i + ∑ v_i ≤ 2n` the sharp value is
`5 ^ (n/2)` for BOTH parities, which is strictly weaker than the odd branch here
(`5 ^ (3/2) = 11.18… > 10`).
-/

namespace Statements.BlockProductOptimum

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (l : List (ℕ × ℕ)),
    (l.map Prod.fst).sum ≤ n → (l.map Prod.snd).sum ≤ n →
      (Even n → (l.map (fun p => p.1 * p.2 + 1)).prod ≤ 5 ^ (n / 2)) ∧
      (Odd n → (l.map (fun p => p.1 * p.2 + 1)).prod ≤ 2 * 5 ^ ((n - 1) / 2))

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.BlockProductOptimum
