import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

namespace Submissions.PaleyLocVertexTransitive.SquareAction

open Commons

theorem proof :
    ∀ p : ℕ, Nat.Prime p → p % 4 = 1 →
      (∀ s t : ZMod p, Commons.IsNonzeroSq s → Commons.IsNonzeroSq t →
          Commons.IsNonzeroSq (s * t)) ∧
      (∀ u v : ZMod p, Commons.IsNonzeroSq u → Commons.IsNonzeroSq v →
          ∃ s : ZMod p, Commons.IsNonzeroSq s ∧ s * u = v) ∧
      (∀ s u v : ZMod p, Commons.IsNonzeroSq s →
          (Commons.IsNonzeroSq (s * u - s * v) ↔ Commons.IsNonzeroSq (u - v))) ∧
      (∀ u v : ZMod p, Commons.IsNonzeroSq (u - v) → Commons.IsNonzeroSq (v - u)) ∧
      (∀ u : ZMod p, ¬ Commons.IsNonzeroSq (u - u)) := by
  intro p hp hp4
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hmul : ∀ s t : ZMod p, Commons.IsNonzeroSq s → Commons.IsNonzeroSq t →
      Commons.IsNonzeroSq (s * t) := by
    rintro s t ⟨hs0, a, rfl⟩ ⟨ht0, b, rfl⟩
    exact ⟨mul_ne_zero hs0 ht0, a * b, by ring⟩
  have hinv : ∀ s : ZMod p, Commons.IsNonzeroSq s → Commons.IsNonzeroSq s⁻¹ := by
    rintro s ⟨hs0, a, rfl⟩
    have ha : a ≠ 0 := by
      intro h; exact hs0 (by rw [h]; ring)
    refine ⟨inv_ne_zero hs0, a⁻¹, ?_⟩
    field_simp
  have hneg : Commons.IsNonzeroSq (-1 : ZMod p) := by
    have h1 : (-1 : ZMod p) ≠ 0 := by simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
    have hsq : IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]; omega
    exact ⟨h1, hsq⟩
  refine ⟨hmul, ?_, ?_, ?_, ?_⟩
  · intro u v hu hv
    have hu0 : u ≠ 0 := hu.1
    refine ⟨v * u⁻¹, hmul _ _ hv (hinv u hu), ?_⟩
    field_simp
  · intro s u v hs
    constructor
    · intro h
      have hs0 : s ≠ 0 := hs.1
      have he : s * u - s * v = s * (u - v) := by ring
      rw [he] at h
      have := hmul _ _ (hinv s hs) h
      have h2 : s⁻¹ * (s * (u - v)) = u - v := by field_simp
      rwa [h2] at this
    · intro h
      have he : s * u - s * v = s * (u - v) := by ring
      rw [he]
      exact hmul _ _ hs h
  · intro u v h
    have he : v - u = (-1) * (u - v) := by ring
    rw [he]
    exact hmul _ _ hneg h
  · intro u h
    exact h.1 (by ring)

end Submissions.PaleyLocVertexTransitive.SquareAction
