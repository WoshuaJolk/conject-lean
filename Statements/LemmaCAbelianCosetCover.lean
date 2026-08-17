import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.BigOperators

/-!
# LemmaCAbelianCosetCover — Lemma C for finite abelian groups

For every finite abelian `G` and every partition of `G` into cosets with a single hole at the
identity, `|G| ≤ ∏ (c_i + 1)` over the distinct used subgroups with multiplicities.

SCOPE WARNING, load-bearing. This statement lives on the subgroup lattice, which exists only
under a regular group action on the index set of a set pair system. It is NOT the posed
problem and does NOT imply it: there is no known reduction from a general 1-cross
intersecting set pair system to the group-invariant case.
-/

namespace Statements.LemmaCAbelianCosetCover

/-- The `p`-th part, written without pointwise-set machinery: the left coset
`rep p • H p.1 = {x | (rep p)⁻¹ * x ∈ H p.1}`. -/
def part {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) (p : (i : Fin r) × Fin (c i)) : Set G :=
  {x : G | (rep p)⁻¹ * x ∈ H p.1}

/-- An exact coset cover of `G` with a single hole at the identity. `H` is injective, so the
`H i` are the DISTINCT used subgroups and `c i` is the multiplicity of `H i`. The parts avoid
the identity, are pairwise disjoint, and together with the hole `{1}` they cover `G`. -/
def IsHoleCover {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) : Prop :=
  Function.Injective H ∧
  (∀ p, (1 : G) ∉ part H c rep p) ∧
  (∀ p q, p ≠ q → Disjoint (part H c rep p) (part H c rep q)) ∧
  (⋃ p, part H c rep p) ∪ {1} = Set.univ

/-- LEMMA C. -/
abbrev statement : Prop :=
  ∀ (G : Type) [CommGroup G] [Finite G] (r : ℕ) (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G),
    IsHoleCover H c rep → Nat.card G ≤ ∏ i, (c i + 1)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.LemmaCAbelianCosetCover
