import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# FranklSingletonCase — a concrete base case for smoke testing

The family F = {∅, {0}} over ℕ is union-closed, nonempty, and has a nonempty member.
Element 0 appears in 1 of 2 sets, so 1 * 2 = 2 ≥ 2.
This is the tight case: 1/2 is attained.
-/

namespace Statements.FranklSingletonCase

abbrev statement : Prop :=
  ∃ (F : Finset (Finset ℕ)),
    F.Nonempty ∧
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
    (∃ A ∈ F, A.Nonempty) ∧
    ∃ x : ℕ, (F.filter (fun A => x ∈ A)).card * 2 ≥ F.card

theorem target : statement := sorry

end Statements.FranklSingletonCase
