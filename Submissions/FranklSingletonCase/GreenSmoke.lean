import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Submissions.FranklSingletonCase.GreenSmoke

theorem proof :
    ∃ (F : Finset (Finset ℕ)),
      F.Nonempty ∧
      (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
      (∃ A ∈ F, A.Nonempty) ∧
      ∃ x : ℕ, (F.filter (fun A => x ∈ A)).card * 2 ≥ F.card := by
  refine ⟨{∅, {0}}, ?_, ?_, ?_, ?_⟩
  · simp [Finset.Nonempty]
  · decide
  · exact ⟨{0}, by decide, by decide⟩
  · refine ⟨0, ?_⟩; decide

end Submissions.FranklSingletonCase.GreenSmoke
