import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Commons.SetPairSystem

/-!
# AnyGroupCosetCover, proved

No commutativity anywhere.  Three separate facts.

* The equivariance of `B` gives the dictionary `x ∈ B g ↔ g⁻¹ • x ∈ B 1`, so the exactness
  clause `(A 1 ∩ B g).card = 1` says exactly one `x ∈ A 1` has `g⁻¹ • x ∈ B 1`.  That is
  clause (i), the exact cover of `G ∖ {1}` by the sets `V(x,y) = {g | g⁻¹ • x = y}`.
* `A 1 ∩ B 1 = ∅` puts the identity in no part; that is clause (ii).
* `d * g⁻¹ ∈ stabilizer G x ↔ d • (g⁻¹ • x) = x ↔ g⁻¹ • x = d⁻¹ • x`, which is clause (iii):
  each part is the right coset `(stabilizer G x) * d`.  This is where the abelian argument
  used commutativity to get a LEFT coset of a stabiliser that is constant along the orbit;
  neither is available here, and neither is needed for the three clauses themselves.
-/

namespace Submissions.AnyGroupCosetCover.RightCosetCover

open MulAction

theorem proof :
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
            (g⁻¹ • x = y ↔ d * g⁻¹ ∈ MulAction.stabilizer G x)) := by
  intro G X _ _ _ _ _ A B _hA hB hAB hcross
  classical
  -- the membership dictionary
  have hdict : ∀ (g : G) (x : X), x ∈ B g ↔ g⁻¹ • x ∈ B 1 := by
    intro g x
    have h : B g = (B 1).image (fun z => g • z) := by have := hB g 1; simpa using this
    rw [h, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro hx; exact ⟨g⁻¹ • x, hx, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have hcard := hcross 1 g (Ne.symm hg)
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
    have hxm : x ∈ A 1 ∩ B g := by rw [hx]; exact Finset.mem_singleton_self x
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.1 hxm
    refine ⟨(x, g⁻¹ • x), ⟨hxA, (hdict g x).1 hxB, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨hx'A, hy'B, hxy'⟩
    dsimp only at hx'A hy'B hxy'
    have hx'B : x' ∈ B g := (hdict g x').2 (by rw [hxy']; exact hy'B)
    have : x' ∈ A 1 ∩ B g := Finset.mem_inter.2 ⟨hx'A, hx'B⟩
    have hxx : x' = x := by
      rw [hx] at this; exact Finset.mem_singleton.1 this
    have hy : y' = g⁻¹ • x := by rw [← hxy', hxx]
    simp [hxx, hy]
  · intro x hxA y hyB h
    have hxy : x = y := by simpa using h
    have hmem : x ∈ A 1 ∩ B 1 := Finset.mem_inter.2 ⟨hxA, by rw [hxy]; exact hyB⟩
    rw [hAB 1] at hmem
    simp at hmem
  · intro x y d g hd
    constructor
    · intro h
      have h1 : d • (g⁻¹ • x) = x := by rw [h, ← hd, smul_inv_smul]
      rw [mem_stabilizer_iff, mul_smul]
      exact h1
    · intro h
      rw [mem_stabilizer_iff, mul_smul] at h
      rw [← hd]
      calc g⁻¹ • x = d⁻¹ • (d • (g⁻¹ • x)) := by rw [inv_smul_smul]
        _ = d⁻¹ • x := by rw [h]

end Submissions.AnyGroupCosetCover.RightCosetCover
