import Commons.SetPairSystem

/-!
# StepTwoRecursion — the residual of the whole page

`m(n+2, n+2, 1) ≤ 5 * m(n, n, 1)`, the existential standing in for the maximum. With the two
base values `m(0,0,1) = 1` and `m(1,1,1) = 2` this implies the root bound by induction in steps
of two; and given Füredi–Gyárfás–Király Proposition 1.1 (supermultiplicativity) the root implies
it back, so the two are equivalent and both are equivalent to the exact recursion
`m(n+2,n+2,1) = 5 * m(n,n,1)`, whose `≥` half is already a theorem.

Three dead routes on this problem name this statement as their residual.
-/

namespace Statements.StepTwoRecursion

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (n m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS (n + 2) (n + 2) m A B →
      ∃ (m' : ℕ) (A' B' : Fin m' → Finset ℕ),
        Commons.OneCrossSPS n n m' A' B' ∧ m ≤ 5 * m'

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.StepTwoRecursion
