import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-!
# Minimum degree three in the third-factor non-orthogonality graph of a UPB

For nonzero `v : Fin 2 → ℂ` put `pp v = ![star (v 1), −star (v 0)]`; it is nonzero, annihilates
`v`, and annihilates every vector proportional to `v`.  If `z_i` were orthogonal to every `z_m`
with `m` outside `{i, j₁, j₂}`, then `a = pp (u j₁)`, `b = pp (w i)`, `c = z_i` would be a
nonzero product vector orthogonal to the whole family.
-/

namespace Submissions.UPBDegreeThree224k.Degree

/-- The annihilator of a vector in `C²`, written out. -/
def pp (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![star (v 1), -star (v 0)]

theorem pp_ne {v : Fin 2 → ℂ} (hv : v ≠ 0) : pp v ≠ 0 := by
  intro h
  apply hv
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [pp] at h0 h1
  funext i
  fin_cases i
  · simpa using h1
  · simpa using h0

theorem pp_self (v : Fin 2 → ℂ) : (∑ r, star (v r) * pp v r) = 0 := by
  rw [Fin.sum_univ_two]
  simp only [pp, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem pp_par {v v' : Fin 2 → ℂ} (h : v 0 * v' 1 - v 1 * v' 0 = 0) :
    (∑ r, star (v' r) * pp v r) = 0 := by
  have h' : star (v 0) * star (v' 1) - star (v 1) * star (v' 0) = 0 := by
    have hh : star (v 0 * v' 1 - v 1 * v' 0) = star (0 : ℂ) := by rw [h]
    simpa [star_sub, star_mul'] using hh
  rw [Fin.sum_univ_two]
  simp only [pp, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination -h'

theorem proof :
  ∀ k : ℕ, 2 ≤ k →
    ∀ u : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ w : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ z : Fin (4 * k + 2) → Fin (4 * k - 1) → ℂ,
      (∀ i, u i ≠ 0) →
      (∀ i, w i ≠ 0) →
      (∀ i, z i ≠ 0) →
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) →
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
        ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0) →
      ∀ i j₁ j₂ : Fin (4 * k + 2),
        u j₁ 0 * u j₂ 1 - u j₁ 1 * u j₂ 0 = 0 →
        ∃ j, j ≠ i ∧ j ≠ j₁ ∧ j ≠ j₂ ∧
          (∑ r, star (z i r) * z j r) ≠ 0 ∧
          ((∑ r, star (u i r) * u j r) = 0 ∨ (∑ r, star (w i r) * w j r) = 0) := by
  intro k _ u w z hu hw hz horth hun i j₁ j₂ hpar
  by_contra hno
  push_neg at hno
  have h0 : ∀ m, m ≠ i → m ≠ j₁ → m ≠ j₂ → (∑ r, star (z i r) * z m r) = 0 := by
    intro m hmi hm1 hm2
    by_contra hne
    have hPQ := hno m hmi hm1 hm2 hne
    rcases mul_eq_zero.1 (horth i m (Ne.symm hmi)) with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact hPQ.1 h'
      · exact hPQ.2 h'
    · exact hne h
  have hker : ∀ m, m ≠ i → m ≠ j₁ → m ≠ j₂ → (∑ r, star (z m r) * z i r) = 0 := by
    intro m hmi hm1 hm2
    have hh : star (∑ r, star (z i r) * z m r) = star (0 : ℂ) := by rw [h0 m hmi hm1 hm2]
    simpa [star_sum, star_mul', mul_comm] using hh
  obtain ⟨m, hm⟩ := hun (pp (u j₁)) (pp_ne (hu j₁)) (pp (w i)) (pp_ne (hw i)) (z i) (hz i)
  by_cases hm1 : m = j₁
  · subst hm1; exact hm (by rw [pp_self]; ring)
  · by_cases hm2 : m = j₂
    · subst hm2; exact hm (by rw [pp_par hpar]; ring)
    · by_cases hmi : m = i
      · subst hmi; exact hm (by rw [pp_self]; ring)
      · exact hm (by rw [hker m hmi hm1 hm2]; ring)

end Submissions.UPBDegreeThree224k.Degree
