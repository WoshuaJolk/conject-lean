import Mathlib

/-!
# The (1,1) tropical Hodge classes of Zharkov's family are exactly `ℤ·c`

Fifteen instances of the symmetry hypothesis, read off with `simp [gammaGen]`, force
`v l j = (v 0 0) · δ_{lj}`.  The only place positivity of `d` is used is to cancel `d` from
`d·W₃₀ = 0`, `d·W₂₁ = 0` and `2d·W₂₀ = 0`.
-/

namespace Submissions.TropicalNS.NS

abbrev G2 : Type := Fin 4 → ℤ
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

theorem proof :
    ∀ (d : ℤ), 0 < d → ∀ (v : Fin 4 → G2),
      (∀ i j m : Fin 4,
          ∑ l : Fin 4, gammaGen d l i m * v l j = ∑ l : Fin 4, gammaGen d l j m * v l i) →
      ∃ k : ℤ, ∀ l j : Fin 4, v l j = if l = j then k else 0 := by
  intro d hd v h
  have hd0 : d ≠ 0 := hd.ne'
  have E : ∀ i j m : Fin 4,
      ∑ l : Fin 4, gammaGen d l i m * v l j = ∑ l : Fin 4, gammaGen d l j m * v l i := h
  -- read off the fifteen instances we need
  have e010 := E 0 1 0
  have e011 := E 0 1 1
  have e012 := E 0 1 2
  have e013 := E 0 1 3
  have e020 := E 0 2 0
  have e021 := E 0 2 1
  have e023 := E 0 2 3
  have e030 := E 0 3 0
  have e031 := E 0 3 1
  have e033 := E 0 3 3
  have e120 := E 1 2 0
  have e121 := E 1 2 1
  have e122 := E 1 2 2
  have e123 := E 1 2 3
  have e133 := E 1 3 3
  simp only [gammaGen, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three] at e010 e011 e012 e013 e020 e021 e023 e030 e031 e033 e120 e121 e122 e123 e133
  -- the substitution chain
  have h01 : v 0 1 = 0 := by linarith [e010]
  have h10 : v 1 0 = 0 := by linarith [e012]
  have h03 : v 0 3 = 0 := by linarith [e030]
  have h32 : v 3 2 = 0 := by linarith [e023, h10]
  have h23 : v 2 3 = 0 := by linarith [e133, h01]
  have h12 : v 1 2 = 0 := by linarith [e122]
  have h30 : v 3 0 = 0 := by
    have : d * v 3 0 = 0 := by linarith [e021, h12]
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hd0
    · exact h'
  have h21 : v 2 1 = 0 := by
    have : d * v 2 1 = 0 := by linarith [e120]
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hd0
    · exact h'
  have h20 : v 2 0 = 0 := by
    have hA : v 0 2 = d * v 2 0 := by linarith [e020]
    have hB : v 0 2 = d * v 3 1 := by linarith [e121]
    have hC : v 3 1 = - v 2 0 := by linarith [e013]
    have : d * v 2 0 + d * v 2 0 = 0 := by rw [hC] at hB; linarith [hA, hB]
    have h2 : (2 * d) * v 2 0 = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h' | h'
    · exact absurd h' (by intro hh; apply hd0; linarith)
    · exact h'
  have h02 : v 0 2 = 0 := by have := e020; rw [h20] at this; linarith
  have h31 : v 3 1 = 0 := by linarith [e013, h20]
  have h13 : v 1 3 = 0 := by linarith [e031, h20]
  have h11 : v 1 1 = v 0 0 := by linarith [e011]
  have h22 : v 2 2 = v 0 0 := by linarith [e123, h11]
  have h33 : v 3 3 = v 0 0 := by linarith [e033]
  refine ⟨v 0 0, ?_⟩
  intro l j
  fin_cases l <;> fin_cases j <;>
    simp_all

end Submissions.TropicalNS.NS
