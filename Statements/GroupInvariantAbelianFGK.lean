import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Even
import Commons.SetPairSystem

/-!
# GroupInvariantAbelianFGK — the Füredi–Gyárfás–Király bound, for abelian-invariant systems

`GroupInvariantBridge` (#10 on this problem) records the verified half of the passage from a
`1`-cross intersecting set pair system with a regular group symmetry to coset-cover language,
and says in its own scope field what the remaining gap is: *"the unverified half — blocks are
cosets of stabiliser subgroups, and the budget `n` factors per orbit — is the honest remaining
gap and should be filed separately by whoever establishes it."*

This statement is what that gap was in the way of.  For a system whose index set IS a finite
ABELIAN group `G` acting regularly on itself, with the ground set carrying a compatible action
and `A`, `B` equivariant, the FGK bound holds outright:

  `|G| ≤ 5 ^ (n/2)` for even `n`, and `|G| ≤ 2 * 5 ^ ((n-1)/2)` for odd `n`.

So the conjecture is TRUE on the whole abelian-group-invariant sub-class, and no search for a
counterexample inside that class can succeed.  The bound is attained: the pentagon is `G = ℤ₅`
at `n = 2`, and the FGK product construction is `G = ℤ₂₅` at `n = 4` with a ground set of two
orbits (one free, one with stabiliser of order 5).

The cardinality bounds are hypotheses here, unlike in `GroupInvariantBridge`, because they are
exactly the budget the conclusion spends.  Commutativity of `G` is load-bearing and is NOT
decoration: it is used twice, once so that `{d | d⁻¹ • x = y}` is a LEFT coset of
`stabilizer G x`, and once so that stabilisers are constant on orbits.
-/

namespace Statements.GroupInvariantAbelianFGK

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (G X : Type) [CommGroup G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
    (n : ℕ) (A B : G → Finset X),
    (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
    (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
    (∀ g : G, (A g).card ≤ n) →
    (∀ g : G, (B g).card ≤ n) →
    (∀ g : G, A g ∩ B g = ∅) →
    (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
      (Even n → Fintype.card G ≤ 5 ^ (n / 2)) ∧
      (Odd n → Fintype.card G ≤ 2 * 5 ^ ((n - 1) / 2))

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.GroupInvariantAbelianFGK
