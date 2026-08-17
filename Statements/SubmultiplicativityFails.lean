import Commons.SetPairSystem

/-!
# SubmultiplicativityFails — `m(a,b,1)` is not submultiplicative

Certificate that the product bound `m(a+a', b+b', 1) ≤ m(a,b,1) * m(a',b',1)` fails, at the
single split `(1,1) + (1,1)`: the first conjunct is `m(1,1,1) ≤ 2`, the second is
`m(2,2,1) ≥ 5`, and `5 > 4 = 2 * 2`. Füredi–Gyárfás–Király Proposition 1.1 gives the reverse
(supermultiplicative) inequality, and it is strict already here, which is exactly why no
product-splitting upper bound can exist.
-/

namespace Statements.SubmultiplicativityFails

/-- The canonical proposition. -/
abbrev statement : Prop :=
  (∀ (m : ℕ) (A B : Fin m → Finset ℕ), Commons.OneCrossSPS 1 1 m A B → m ≤ 2) ∧
  (∃ A B : Fin 5 → Finset ℕ, Commons.OneCrossSPS 2 2 5 A B)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.SubmultiplicativityFails
