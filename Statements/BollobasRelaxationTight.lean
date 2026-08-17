import Mathlib.Data.Nat.Choose.Basic
import Commons.SetPairSystem

/-!
# BollobasRelaxationTight — the cross-intersecting relaxation is attained at `C(2n,n)`

Weaken the cross clause of `Commons.OneCrossSPS` from `(A i ∩ B j).card = 1` to
`(A i ∩ B j).Nonempty` and Bollobás' bound `C(a+b,a)` becomes attained: on ground set `[2n]`,
take the `A`-family to run over all `n`-subsets with each `B` the complement of its `A`. So
the relaxation's growth constant is exactly `4`, and any argument invariant under that
weakening cannot move the upper end of this problem's squeeze at all.
-/

namespace Statements.BollobasRelaxationTight

/-- Bollobás' relaxation: the cross clause weakened to `Nonempty`. -/
def CrossSPS (a b m : ℕ) (A B : Fin m → Finset ℕ) : Prop :=
  (∀ i, (A i).card ≤ a) ∧
  (∀ i, (B i).card ≤ b) ∧
  (∀ i, A i ∩ B i = ∅) ∧
  (∀ i j, i ≠ j → (A i ∩ B j).Nonempty)

/-- The canonical proposition: the relaxation is attained at `C(2n, n)` for every `n`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∃ A B : Fin ((2 * n).choose n) → Finset ℕ,
    CrossSPS n n ((2 * n).choose n) A B

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.BollobasRelaxationTight
