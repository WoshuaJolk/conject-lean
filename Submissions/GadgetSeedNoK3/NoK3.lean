import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

namespace Submissions.GadgetSeedNoK3.NoK3

open scoped BigOperators

noncomputable section

abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

abbrev statement : Prop :=
  ¬ ∃ (M : Fin 3 → Fin 3 → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0)

theorem target : statement := by
  rintro ⟨M, c, hc, hdiag, hoff, hpair⟩
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hterm : star (M 0 2) * M 1 2 = 0 := by
    have h := hpair 0 1
    simp only [h01, ↓reduceIte] at h
    simpa [pair, Fin.sum_univ_three, hdiag 0, hdiag 1] using h
  have h02nz : M 0 2 ≠ 0 := hoff 0 2 h02
  have h12nz : M 1 2 ≠ 0 := hoff 1 2 h12
  have hstar02nz : star (M 0 2) ≠ 0 := by
    intro hz
    apply h02nz
    exact star_eq_zero.mp hz
  exact (mul_ne_zero hstar02nz h12nz) hterm

end
end Submissions.GadgetSeedNoK3.NoK3
