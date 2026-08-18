import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Ineq

set_option maxRecDepth 100000

namespace Submissions.TwinPrimesSmallCases.KernelData

/-- The concrete twin-prime data below 200, the offset guards, and two explicit twin pairs
above `10 ^ 5` and `10 ^ 6`.  The finite parts go to the kernel by `decide`; the two
witnesses are named and their primality is certified by `norm_num`. -/
theorem proof :
  ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
      = ({3, 5, 11, 17, 29, 41, 59, 71} : Finset ℕ))
  ∧ ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card = 8
  ∧ ((Finset.range 200).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card = 15
  ∧ (∀ p ∈ Finset.range 3, ¬ (Nat.Prime p ∧ Nat.Prime (p + 2)))
  ∧ (Nat.Prime 7 ∧ ¬ Nat.Prime 9)
  ∧ ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 1)) = ({2} : Finset ℕ))
  ∧ ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 4))).card = 9
  ∧ (∃ p : ℕ, 100000 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
  ∧ (∃ p : ℕ, 1000000 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    ⟨100151, by norm_num, by norm_num, by norm_num⟩,
    ⟨1000037, by norm_num, by norm_num, by norm_num⟩⟩

end Submissions.TwinPrimesSmallCases.KernelData
