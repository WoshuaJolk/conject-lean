import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Commons.SetPairSystem

/-!
# TowerInductionBlocked, proved

The witness, found by exhaustive enumeration over `ℤ/10` and then checked here by the kernel:

* family 1: `K₁ = {0,5}` (the subgroup of order 2), `A₁ = {0}`, `B₁ = {1,2,3}` — three disjoint
  cosets of `K₁`, covering `{2,3,4,7,8,9}`;
* family 2: `K₂ = {0}`, `A₂ = {0,1,6}`, `B₂ = {5}` — three singletons, covering `{1,5,6}`.

Together they partition `ℤ/10 ∖ {0}`.  `{0,2,3,4,7,8,9}` is not closed (`2+3 = 5`), and
`{0,1,5,6}` is not closed (`1+1 = 2`).  Everything is a finite check on ten elements.
-/

namespace Submissions.TowerInductionBlocked.ZModTen

def blk (A K B : Finset (ZMod 10)) : Finset (ZMod 10) :=
  (A ×ˢ K ×ˢ B).image (fun p => p.1 + p.2.1 - p.2.2)

theorem proof :
    ∃ K₁ A₁ B₁ K₂ A₂ B₂ : Finset (ZMod 10),
      ((0 : ZMod 10) ∈ K₁ ∧ ∀ x ∈ K₁, ∀ y ∈ K₁, x - y ∈ K₁) ∧
      ((0 : ZMod 10) ∈ K₂ ∧ ∀ x ∈ K₂, ∀ y ∈ K₂, x - y ∈ K₂) ∧
      (blk A₁ K₁ B₁).card = A₁.card * K₁.card * B₁.card ∧
      (blk A₂ K₂ B₂).card = A₂.card * K₂.card * B₂.card ∧
      1 < K₁.card ∧
      (blk A₁ K₁ B₁) ∩ (blk A₂ K₂ B₂) = ∅ ∧
      (blk A₁ K₁ B₁) ∪ (blk A₂ K₂ B₂) = Finset.univ.erase 0 ∧
      (¬ ∀ x ∈ insert (0 : ZMod 10) (blk A₁ K₁ B₁), ∀ y ∈ insert (0 : ZMod 10) (blk A₁ K₁ B₁),
          x + y ∈ insert (0 : ZMod 10) (blk A₁ K₁ B₁)) ∧
      (¬ ∀ x ∈ insert (0 : ZMod 10) (blk A₂ K₂ B₂), ∀ y ∈ insert (0 : ZMod 10) (blk A₂ K₂ B₂),
          x + y ∈ insert (0 : ZMod 10) (blk A₂ K₂ B₂)) := by
  refine ⟨{0, 5}, {0}, {1, 2, 3}, {0}, {0, 1, 6}, {5},
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Submissions.TowerInductionBlocked.ZModTen
