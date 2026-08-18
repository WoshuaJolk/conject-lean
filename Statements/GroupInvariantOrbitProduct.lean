import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Commons.SetPairSystem

/-!
# GroupInvariantOrbitProduct — the one lemma that upgrades the abelian case

`GroupInvariantAbelianFGK` (#19) proves the Füredi–Gyárfás–Király bound for systems invariant
under a finite ABELIAN group, and `AnyGroupCosetCover` (#21) shows that the structural half of
that proof needs no commutativity: the sets `{g | g⁻¹ • x = y}` always partition `G ∖ {1}` into
right cosets of stabilisers.  What commutativity bought was the COUNTING, and this statement is
exactly the counting, for an arbitrary finite group:

  `|G| ≤ ∏_ω (a ω * b ω + 1)`,

the product over `G`-orbits `ω` of the ground set, where `a ω = |A 1 ∩ ω|` and `b ω = |B 1 ∩ ω|`.

Orbits are named by an arbitrary `π : X → Ω` with `π x = π y ↔ ∃ g, g • x = y`, so no quotient
type and no `Decidable` instance on a quotient enters the proposition.

**Status.** PROVED for abelian `G` — that is the content of #19, where the parts of one orbit are
cosets of a single subgroup and `LemmaCAbelianCosetCover` (#5) applies.  OPEN in general.  With
`BlockProductOptimum` (#15) it yields the FGK bound for every group-invariant system, and that
implication is itself machine-checked as `GroupInvariantFGKFromOrbitProduct`.

**Equivalent group-theoretic form, with no set pair systems in it.**  Suppose `G ∖ {1}` is exactly
partitioned by the sets `t_{j,i} * K_j * s_{j,k}` for subgroups `K_j ≤ G` and elements
`t_{j,1..a_j}`, `s_{j,1..b_j}`.  Then `|G| ≤ ∏_j (a_j * b_j + 1)`.  The dictionary is
`x = t_{j,i} K_j`, `y = s_{j,k}⁻¹ K_j`, and `{g | g⁻¹ • x = y} = t_{j,i} K_j s_{j,k}`.  For abelian
`G` a sandwich `t K s` is the coset `K(ts)` and the statement is Lemma C with the multiplicities
of one orbit merged; in general `t K s` is a coset of the CONJUGATE `t K t⁻¹`, which is why
Lemma C read per distinct subgroup is too weak (see #21).
-/

namespace Statements.GroupInvariantOrbitProduct

/-- The canonical proposition. -/
abbrev statement : Prop :=
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

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.GroupInvariantOrbitProduct
