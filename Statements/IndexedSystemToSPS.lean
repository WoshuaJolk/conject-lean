import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Commons.SetPairSystem

/-!
# IndexedSystemToSPS — the relabelling bridge

`Commons.OneCrossSPS` fixes the index set to `Fin m` and the ground set to `ℕ`.  Every
statement on this problem that reasons about a system indexed by some other finite type — a
group acting on itself, a quotient, a product — needs to know that this loses nothing.  This
statement is that fact, and it is what makes such a statement's bound a bound on `m(a,b,1)`.

Given ANY finite index type `I` and ANY finite ground type `X` carrying the four clauses with
budgets `a` and `b`, there is a `Commons.OneCrossSPS a b (Fintype.card I)` on the ground set
`ℕ`.  No structure on `I` or `X` is used: the content is that all four clauses are stated in
terms of cardinalities and intersections, both of which an injection preserves and reflects.

Consequently a bound proved for systems indexed by, say, an abelian group `G` acting
regularly is literally a bound on `m(a,b,1)` restricted to systems with that symmetry, with
`m = Fintype.card G`.  Without this the relevance of such a bound is invisible.
-/

namespace Statements.IndexedSystemToSPS

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (I X : Type) [Fintype I] [Fintype X] [DecidableEq X] (a b : ℕ) (A B : I → Finset X),
    (∀ i, (A i).card ≤ a) →
    (∀ i, (B i).card ≤ b) →
    (∀ i, A i ∩ B i = ∅) →
    (∀ i j, i ≠ j → (A i ∩ B j).card = 1) →
      ∃ A' B' : Fin (Fintype.card I) → Finset ℕ,
        Commons.OneCrossSPS a b (Fintype.card I) A' B'

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.IndexedSystemToSPS
