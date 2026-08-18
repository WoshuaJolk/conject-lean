import Commons.SetPairSystem

/-!
# ProductConstruction — Füredi–Gyárfás–Király Proposition 1.1, formalized

If an `(a₁,b₁)`-bounded 1-cross intersecting set pair system of size `m₁` exists and an
`(a₂,b₂)`-bounded one of size `m₂` exists, then an `(a₁+a₂, b₁+b₂)`-bounded one of size
`m₁ · m₂` exists.

Construction: take `m₂` pairwise disjoint copies of the first system, one attached to each
index `i` of the second, and set

    A_{i,j} = A¹_j ⊔ A²_i,      B_{i,j} = B¹_j ⊔ B²_i,

with the copies of the inner ground set disjoint from each other and from the outer one.
Then `A_{i,j} ∩ B_{i',j'}` picks up the inner witness when `i = i'` (and `j ≠ j'`) and the
outer witness when `i ≠ i'`, never both, so it always has exactly one element.

This is the engine of the whole lower-bound side of this problem: iterating it from the
pentagon `H(2,2)` gives the `5^(n/2)` construction of Corollary 1.2, and it is what turns
any single small block into a symmetric counterexample.  It is cited by
SubmultiplicativityFails and by StepTwoRecursion's prose, and until now it was not itself
on the board.
-/

namespace Statements.ProductConstruction

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (a₁ b₁ m₁ a₂ b₂ m₂ : ℕ) (A₁ B₁ : Fin m₁ → Finset ℕ) (A₂ B₂ : Fin m₂ → Finset ℕ),
    Commons.OneCrossSPS a₁ b₁ m₁ A₁ B₁ →
    Commons.OneCrossSPS a₂ b₂ m₂ A₂ B₂ →
      ∃ A B : Fin (m₁ * m₂) → Finset ℕ,
        Commons.OneCrossSPS (a₁ + a₂) (b₁ + b₂) (m₁ * m₂) A B

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ProductConstruction
