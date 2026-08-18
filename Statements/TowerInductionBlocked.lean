import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Commons.SetPairSystem

/-!
# TowerInductionBlocked — the natural induction on `GroupInvariantOrbitProduct` does not start

`GroupInvariantOrbitProduct` (#22) says that if `G ∖ {1}` is exactly partitioned into families
of sandwich cosets `t_{j,i} K_j s_{j,k}`, then `|G| ≤ ∏_j (a_j b_j + 1)`.  The obvious proof
attempt — and it is what the abelian proof of `LemmaCAbelianCosetCover` does, via a coatom — is
to find a sub-collection of the families whose parts, together with the identity, form a proper
subgroup `M`, and then induct on the tower `G ⊃ M ⊃ …`, paying one factor `a_j b_j + 1` per step.

This statement is a certificate that the induction does not start in general: an exact
two-family cover of `ℤ/10 ∖ {0}` in which NEITHER family, with `0` adjoined, is closed under
addition.  With two families the only proper nonempty sub-collections are the two singletons, so
no tower step exists at all.

The certificate is not degenerate: one of its two families uses the nontrivial subgroup `{0,5}`,
so this is not an artefact of every stabiliser being trivial (the all-free case of #22 is easy,
since `∏(c_j+1) ≥ 1 + ∑ c_j = |G|` there).  The bound of #22 still holds on it, with slack:
`(1·3+1)(3·1+1) = 16 ≥ 10`.
-/

namespace Statements.TowerInductionBlocked

/-- The block `A + K - B`: the union of the `|A|*|B|` sandwich parts of one family, written
additively. -/
def blk (A K B : Finset (ZMod 10)) : Finset (ZMod 10) :=
  (A ×ˢ K ×ˢ B).image (fun p => p.1 + p.2.1 - p.2.2)

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∃ K₁ A₁ B₁ K₂ A₂ B₂ : Finset (ZMod 10),
    -- `K₁` and `K₂` are subgroups
    ((0 : ZMod 10) ∈ K₁ ∧ ∀ x ∈ K₁, ∀ y ∈ K₁, x - y ∈ K₁) ∧
    ((0 : ZMod 10) ∈ K₂ ∧ ∀ x ∈ K₂, ∀ y ∈ K₂, x - y ∈ K₂) ∧
    -- each family really is `|A|*|B|` PAIRWISE DISJOINT cosets of its subgroup
    (blk A₁ K₁ B₁).card = A₁.card * K₁.card * B₁.card ∧
    (blk A₂ K₂ B₂).card = A₂.card * K₂.card * B₂.card ∧
    -- and at least one of the two subgroups is nontrivial
    1 < K₁.card ∧
    -- the two families exactly partition the nonzero elements
    (blk A₁ K₁ B₁) ∩ (blk A₂ K₂ B₂) = ∅ ∧
    (blk A₁ K₁ B₁) ∪ (blk A₂ K₂ B₂) = Finset.univ.erase 0 ∧
    -- yet NEITHER family, with `0` adjoined, is closed under addition
    (¬ ∀ x ∈ insert (0 : ZMod 10) (blk A₁ K₁ B₁), ∀ y ∈ insert (0 : ZMod 10) (blk A₁ K₁ B₁),
        x + y ∈ insert (0 : ZMod 10) (blk A₁ K₁ B₁)) ∧
    (¬ ∀ x ∈ insert (0 : ZMod 10) (blk A₂ K₂ B₂), ∀ y ∈ insert (0 : ZMod 10) (blk A₂ K₂ B₂),
        x + y ∈ insert (0 : ZMod 10) (blk A₂ K₂ B₂))

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.TowerInductionBlocked
