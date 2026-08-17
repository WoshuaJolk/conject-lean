import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# GroupInvariantBridge — what a regular group action buys, stated exactly

FGK Theorem 1.8 turns an `(n,n)`-bounded `1`-cross intersecting set pair system into an exact
partition of the off-diagonal cells of an `m × m` grid by rectangles `S_x × T_x`, where
`S_x = {i | x ∈ A i}` and `T_x = {j | x ∈ B j}` for a ground element `x`.

Specialise to a system whose index set IS a finite group `G`, carried by a `G`-action on the
ground set for which `A` and `B` are equivariant. Two things happen, and this statement is
exactly those two things:

* **Collapse.** The `|G|(|G|-1)` cell equations are translates of the `|G|-1` equations at the
  identity: `A g ∩ B (g * d) = g • (A 1 ∩ B d)` for every `g` and every `d ≠ 1`. So the
  exactness conditions are indexed by `G \ {1}`, one per non-identity group element.
* **Orbit-constancy.** The block multiplicity `x ↦ #{g | x ∈ A g ∧ x ∈ B (g * d)}` is constant
  on `G`-orbits of the ground set. This is what allows the total `|G|` at each `d ≠ 1` to be
  redistributed over orbit representatives with stabiliser weights `1 / |Stab x|`, giving a
  weighted tiling of `G \ {1}` by one block per orbit.

WHAT THIS DOES NOT SAY, deliberately. It does NOT identify the blocks as cosets, and it does
NOT bound `m(n,n,1)`. See the `scope` field: the coset identification is unproved here, and
one common phrasing of it is false at the pentagon.
-/

namespace Statements.GroupInvariantBridge

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
    (A B : G → Finset X),
    (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
    (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
    (∀ g : G, A g ∩ B g = ∅) →
    (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
    (∀ d : G, d ≠ 1 → ∀ g : G, A g ∩ B (g * d) = (A 1 ∩ B d).image (fun x => g • x))
      ∧ (∀ (d : G) (x : X) (k : G),
          (Finset.univ.filter (fun g : G => x ∈ A g ∧ x ∈ B (g * d))).card
            = (Finset.univ.filter (fun g : G => k • x ∈ A g ∧ k • x ∈ B (g * d))).card)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.GroupInvariantBridge
