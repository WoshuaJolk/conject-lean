import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic
import Commons.SetPairSystem

/-!
# IndexedSystemToSPS, proved

Relabel the index type by `Fintype.equivFin I` and embed the ground type into `ℕ` by
`fun x => (Fintype.equivFin X x : ℕ)`, which is injective.  An injective image commutes with
intersection and preserves cardinality, so all four clauses transport verbatim.
-/

namespace Submissions.IndexedSystemToSPS.Relabel

theorem proof :
    ∀ (I X : Type) [Fintype I] [Fintype X] [DecidableEq X] (a b : ℕ) (A B : I → Finset X),
      (∀ i, (A i).card ≤ a) →
      (∀ i, (B i).card ≤ b) →
      (∀ i, A i ∩ B i = ∅) →
      (∀ i j, i ≠ j → (A i ∩ B j).card = 1) →
        ∃ A' B' : Fin (Fintype.card I) → Finset ℕ,
          Commons.OneCrossSPS a b (Fintype.card I) A' B' := by
  intro I X _ _ _ a b A B hA hB hdisj hcross
  classical
  set e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I with he
  set f : X → ℕ := fun x => ((Fintype.equivFin X x : Fin (Fintype.card X)) : ℕ) with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    have : (Fintype.equivFin X x) = (Fintype.equivFin X y) := Fin.ext hxy
    exact (Fintype.equivFin X).injective this
  refine ⟨fun k => (A (e.symm k)).image f, fun k => (B (e.symm k)).image f, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [Finset.card_image_of_injective _ hfinj]
    exact hA _
  · intro k
    rw [Finset.card_image_of_injective _ hfinj]
    exact hB _
  · intro k
    rw [← Finset.image_inter _ _ hfinj, hdisj (e.symm k)]
    simp
  · intro k l hkl
    have hne : e.symm k ≠ e.symm l := fun h => hkl (by simpa using congrArg e h)
    rw [← Finset.image_inter _ _ hfinj, Finset.card_image_of_injective _ hfinj]
    exact hcross _ _ hne

end Submissions.IndexedSystemToSPS.Relabel
