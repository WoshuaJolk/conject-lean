import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Commons.SetPairSystem

/-!
# AnyGroupCosetCover — the coset-cover reduction, for EVERY finite group

`GroupInvariantAbelianFGK` proves the Füredi–Gyárfás–Király bound for systems invariant under
a finite ABELIAN group, and commutativity is genuinely used there.  This statement isolates
the part of that argument that needs no commutativity at all, so that the non-abelian
frontier is stated exactly rather than gestured at.

Let a finite group `G` act regularly on the index set of a `1`-cross intersecting set pair
system, with a compatible action on the ground set `X` and `A`, `B` equivariant.  Then:

* **(i) Exact cover.** For every `g ≠ 1` there is exactly one pair `(x, y)` with `x ∈ A 1`,
  `y ∈ B 1` and `g⁻¹ • x = y`.  So the sets `V(x,y) = {g | g⁻¹ • x = y}` partition `G ∖ {1}`.
* **(ii) The hole.** The identity lies in no part, because `A 1 ∩ B 1 = ∅`.
* **(iii) Each part is a coset.** If `d⁻¹ • x = y` then `g⁻¹ • x = y ↔ d * g⁻¹ ∈ stabilizer G x`,
  that is `V(x,y) = (stabilizer G x) * d`, a RIGHT coset of the stabiliser.

Clause (iii) is where the abelian and general cases part company, and the statement is filed
so that the parting is on the record.  In an abelian group a right coset is a left coset and
the stabilisers of the points of one orbit are EQUAL, so the parts coming from one orbit are
`aⱼ * bⱼ` cosets of a single subgroup and `LemmaCAbelianCosetCover` closes the argument.  In
a general group the stabilisers along an orbit are only CONJUGATE, so those parts are cosets
of `aⱼ` different subgroups, `bⱼ` apiece.
-/

namespace Statements.AnyGroupCosetCover

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
    (A B : G → Finset X),
    (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
    (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
    (∀ g : G, A g ∩ B g = ∅) →
    (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
      (∀ g : G, g ≠ 1 →
          ∃! p : X × X, p.1 ∈ A 1 ∧ p.2 ∈ B 1 ∧ g⁻¹ • p.1 = p.2) ∧
      (∀ x ∈ A 1, ∀ y ∈ B 1, (1 : G)⁻¹ • x ≠ y) ∧
      (∀ (x y : X) (d g : G), d⁻¹ • x = y →
          (g⁻¹ • x = y ↔ d * g⁻¹ ∈ MulAction.stabilizer G x))

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.AnyGroupCosetCover
