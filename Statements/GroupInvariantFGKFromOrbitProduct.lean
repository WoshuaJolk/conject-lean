import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Even
import Commons.SetPairSystem

/-!
# GroupInvariantFGKFromOrbitProduct — the upgrade, made mechanical

`GroupInvariantOrbitProduct` is the single open lemma standing between
`GroupInvariantAbelianFGK` (#19, abelian only) and the Füredi–Gyárfás–Király bound for EVERY
group-invariant `1`-cross intersecting set pair system.  This statement discharges the rest of
that implication once and for all: assuming the orbit-product bound, the FGK bound follows for
an arbitrary finite group, with no commutativity anywhere.

So whoever proves `GroupInvariantOrbitProduct` gets the group-invariant case of the conjecture
immediately, with nothing further to check.  The remaining content is only the arithmetic — the
per-orbit counts `a ω` sum to `|A 1| ≤ n` and the `b ω` sum to `|B 1| ≤ n`, and
`BlockProductOptimum` (#15) caps `∏ (a ω * b ω + 1)` at the FGK value.
-/

namespace Statements.GroupInvariantFGKFromOrbitProduct

/-- The orbit-product hypothesis, spelled exactly as
`Statements.GroupInvariantOrbitProduct.statement`.  It is restated inline rather than imported
because a canonical statement may not depend on another one. -/
abbrev OrbitProduct : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
    (A B : G → Finset X),
    (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
    (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
    (∀ g : G, A g ∩ B g = ∅) →
    (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
    ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (π : X → Ω),
      (∀ x y : X, π x = π y ↔ ∃ g : G, g • x = y) →
        Fintype.card G ≤
          ∏ ω : Ω, (((A 1).filter (fun x => π x = ω)).card
                    * ((B 1).filter (fun y => π y = ω)).card + 1)

/-- The canonical proposition. -/
abbrev statement : Prop :=
  OrbitProduct →
    ∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
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

end Statements.GroupInvariantFGKFromOrbitProduct
