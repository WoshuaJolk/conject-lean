import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Removal sets a `(4k+2)`-state unextendible family in `C²⊗C²⊗C^(4k−1)` must survive

Three facts, each proved by producing the annihilator explicitly and then having nowhere
for unextendibility to land.  For nonzero `v : Fin 2 → ℂ` put `pp v = ![star (v 1), −star (v 0)]`.
Then `pp v ≠ 0`, `⟨v | pp v⟩ = 0`, and if `v` and `v'` are proportional then `⟨v' | pp v⟩ = 0`
as well.  No orthogonality of the family, no minimality and no construction is used.
-/

namespace Submissions.UPBRemovalSpan224k.Removal

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
  simp only [pp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem pp_par {v v' : Fin 2 → ℂ} (h : v 0 * v' 1 - v 1 * v' 0 = 0) :
    (∑ r, star (v' r) * pp v r) = 0 := by
  have h' : star (v 0) * star (v' 1) - star (v 1) * star (v' 0) = 0 := by
    have hh : star (v 0 * v' 1 - v 1 * v' 0) = star (0 : ℂ) := by rw [h]
    simpa [star_sub, star_mul'] using hh
  rw [Fin.sum_univ_two]
  simp only [pp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linear_combination -h'

theorem proof :
  ∀ k : ℕ, 2 ≤ k →
    ∀ u : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ w : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ z : Fin (4 * k + 2) → Fin (4 * k - 1) → ℂ,
      (∀ i, u i ≠ 0) →
      (∀ i, w i ≠ 0) →
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
        ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0) →
      (∀ i j : Fin (4 * k + 2), ∀ c : Fin (4 * k - 1) → ℂ,
          (∀ l, l ≠ i → l ≠ j → (∑ r, star (z l r) * c r) = 0) → c = 0)
    ∧ (∀ i j l : Fin (4 * k + 2),
          u i 0 * u j 1 - u i 1 * u j 0 = 0 →
          ∀ c : Fin (4 * k - 1) → ℂ,
          (∀ m, m ≠ i → m ≠ j → m ≠ l → (∑ r, star (z m r) * c r) = 0) → c = 0)
    ∧ (∀ i j l : Fin (4 * k + 2),
          w i 0 * w j 1 - w i 1 * w j 0 = 0 →
          ∀ c : Fin (4 * k - 1) → ℂ,
          (∀ m, m ≠ i → m ≠ j → m ≠ l → (∑ r, star (z m r) * c r) = 0) → c = 0) := by
  intro k _ u w z hu hw hun
  refine ⟨?_, ?_, ?_⟩
  · intro i j c hc
    by_contra hc0
    obtain ⟨l, hl⟩ := hun (pp (u i)) (pp_ne (hu i)) (pp (w j)) (pp_ne (hw j)) c hc0
    by_cases hli : l = i
    · subst hli; exact hl (by rw [pp_self]; ring)
    · by_cases hlj : l = j
      · subst hlj; exact hl (by rw [pp_self]; ring)
      · exact hl (by rw [hc l hli hlj]; ring)
  · intro i j l hpar c hc
    by_contra hc0
    obtain ⟨m, hm⟩ := hun (pp (u i)) (pp_ne (hu i)) (pp (w l)) (pp_ne (hw l)) c hc0
    by_cases hmi : m = i
    · subst hmi; exact hm (by rw [pp_self]; ring)
    · by_cases hmj : m = j
      · subst hmj; exact hm (by rw [pp_par hpar]; ring)
      · by_cases hml : m = l
        · subst hml; exact hm (by rw [pp_self]; ring)
        · exact hm (by rw [hc m hmi hmj hml]; ring)
  · intro i j l hpar c hc
    by_contra hc0
    obtain ⟨m, hm⟩ := hun (pp (u l)) (pp_ne (hu l)) (pp (w i)) (pp_ne (hw i)) c hc0
    by_cases hmi : m = i
    · subst hmi; exact hm (by rw [pp_self]; ring)
    · by_cases hmj : m = j
      · subst hmj; exact hm (by rw [pp_par hpar]; ring)
      · by_cases hml : m = l
        · subst hml; exact hm (by rw [pp_self]; ring)
        · exact hm (by rw [hc m hmi hmj hml]; ring)

end Submissions.UPBRemovalSpan224k.Removal
