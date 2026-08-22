import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace Submissions.SpanningOrthRep5Clebsch.Clebsch

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- Integer witness: orthogonality graph exactly the Clebsch graph (Hamming labeling), no six in a common hyperplane. -/
def vZ : Fin 16 → Fin 5 → ℤ := ![
  ![3, 3, -3, -5, -1],
  ![8, -5, 2, 1, -2],
  ![1, 0, -1, 1, 1],
  ![1, 2, 1, 0, 0],
  ![1, 1, -2, 2, 2],
  ![7, 15, 11, -1, 1],
  ![119775, 119775, -340208, 119775, -579758],
  ![2, -1, 0, -1, 0],
  ![0, 1, 3, -1, -1],
  ![2, 2, -1, -2, 1],
  ![26, -4, -11, -18, -19],
  ![1, -1, 1, 0, 1],
  ![5, -3, 1, -1, 1],
  ![119, 44, -103, 69, -291],
  ![245198, 461395, 185784, 81355, 53766],
  ![171, 8, -485, 334, 322]]

def v (i : Fin 16) : Fin 5 → ℂ := fun r => (vZ i r : ℂ)

/-- Bit `k` of a vertex index, as in the statement. -/
abbrev bit (i : Fin 16) (k : Fin 4) : ℕ :=
  (i.val / (2 ^ k.val)) % 2

/-- Hamming distance on `(ℤ/2)^4`, as in the statement. -/
abbrev ham (i j : Fin 16) : ℕ :=
  (if bit i ⟨0, by omega⟩ ≠ bit j ⟨0, by omega⟩ then 1 else 0) +
  (if bit i ⟨1, by omega⟩ ≠ bit j ⟨1, by omega⟩ then 1 else 0) +
  (if bit i ⟨2, by omega⟩ ≠ bit j ⟨2, by omega⟩ then 1 else 0) +
  (if bit i ⟨3, by omega⟩ ≠ bit j ⟨3, by omega⟩ then 1 else 0)

/-- The Clebsch adjacency, restated verbatim. -/
abbrev clebschEdge (i j : Fin 16) : Prop :=
  ham i j = 1 ∨ ham i j = 4

def dot5Z (x y : Fin 5 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4

def det5Z (x y z t u : Fin 5 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 * t 3 * u 4
    - x 0 * y 1 * z 2 * t 4 * u 3
    - x 0 * y 1 * z 3 * t 2 * u 4
    + x 0 * y 1 * z 3 * t 4 * u 2
    + x 0 * y 1 * z 4 * t 2 * u 3
    - x 0 * y 1 * z 4 * t 3 * u 2
    - x 0 * y 2 * z 1 * t 3 * u 4
    + x 0 * y 2 * z 1 * t 4 * u 3
    + x 0 * y 2 * z 3 * t 1 * u 4
    - x 0 * y 2 * z 3 * t 4 * u 1
    - x 0 * y 2 * z 4 * t 1 * u 3
    + x 0 * y 2 * z 4 * t 3 * u 1
    + x 0 * y 3 * z 1 * t 2 * u 4
    - x 0 * y 3 * z 1 * t 4 * u 2
    - x 0 * y 3 * z 2 * t 1 * u 4
    + x 0 * y 3 * z 2 * t 4 * u 1
    + x 0 * y 3 * z 4 * t 1 * u 2
    - x 0 * y 3 * z 4 * t 2 * u 1
    - x 0 * y 4 * z 1 * t 2 * u 3
    + x 0 * y 4 * z 1 * t 3 * u 2
    + x 0 * y 4 * z 2 * t 1 * u 3
    - x 0 * y 4 * z 2 * t 3 * u 1
    - x 0 * y 4 * z 3 * t 1 * u 2
    + x 0 * y 4 * z 3 * t 2 * u 1
    - x 1 * y 0 * z 2 * t 3 * u 4
    + x 1 * y 0 * z 2 * t 4 * u 3
    + x 1 * y 0 * z 3 * t 2 * u 4
    - x 1 * y 0 * z 3 * t 4 * u 2
    - x 1 * y 0 * z 4 * t 2 * u 3
    + x 1 * y 0 * z 4 * t 3 * u 2
    + x 1 * y 2 * z 0 * t 3 * u 4
    - x 1 * y 2 * z 0 * t 4 * u 3
    - x 1 * y 2 * z 3 * t 0 * u 4
    + x 1 * y 2 * z 3 * t 4 * u 0
    + x 1 * y 2 * z 4 * t 0 * u 3
    - x 1 * y 2 * z 4 * t 3 * u 0
    - x 1 * y 3 * z 0 * t 2 * u 4
    + x 1 * y 3 * z 0 * t 4 * u 2
    + x 1 * y 3 * z 2 * t 0 * u 4
    - x 1 * y 3 * z 2 * t 4 * u 0
    - x 1 * y 3 * z 4 * t 0 * u 2
    + x 1 * y 3 * z 4 * t 2 * u 0
    + x 1 * y 4 * z 0 * t 2 * u 3
    - x 1 * y 4 * z 0 * t 3 * u 2
    - x 1 * y 4 * z 2 * t 0 * u 3
    + x 1 * y 4 * z 2 * t 3 * u 0
    + x 1 * y 4 * z 3 * t 0 * u 2
    - x 1 * y 4 * z 3 * t 2 * u 0
    + x 2 * y 0 * z 1 * t 3 * u 4
    - x 2 * y 0 * z 1 * t 4 * u 3
    - x 2 * y 0 * z 3 * t 1 * u 4
    + x 2 * y 0 * z 3 * t 4 * u 1
    + x 2 * y 0 * z 4 * t 1 * u 3
    - x 2 * y 0 * z 4 * t 3 * u 1
    - x 2 * y 1 * z 0 * t 3 * u 4
    + x 2 * y 1 * z 0 * t 4 * u 3
    + x 2 * y 1 * z 3 * t 0 * u 4
    - x 2 * y 1 * z 3 * t 4 * u 0
    - x 2 * y 1 * z 4 * t 0 * u 3
    + x 2 * y 1 * z 4 * t 3 * u 0
    + x 2 * y 3 * z 0 * t 1 * u 4
    - x 2 * y 3 * z 0 * t 4 * u 1
    - x 2 * y 3 * z 1 * t 0 * u 4
    + x 2 * y 3 * z 1 * t 4 * u 0
    + x 2 * y 3 * z 4 * t 0 * u 1
    - x 2 * y 3 * z 4 * t 1 * u 0
    - x 2 * y 4 * z 0 * t 1 * u 3
    + x 2 * y 4 * z 0 * t 3 * u 1
    + x 2 * y 4 * z 1 * t 0 * u 3
    - x 2 * y 4 * z 1 * t 3 * u 0
    - x 2 * y 4 * z 3 * t 0 * u 1
    + x 2 * y 4 * z 3 * t 1 * u 0
    - x 3 * y 0 * z 1 * t 2 * u 4
    + x 3 * y 0 * z 1 * t 4 * u 2
    + x 3 * y 0 * z 2 * t 1 * u 4
    - x 3 * y 0 * z 2 * t 4 * u 1
    - x 3 * y 0 * z 4 * t 1 * u 2
    + x 3 * y 0 * z 4 * t 2 * u 1
    + x 3 * y 1 * z 0 * t 2 * u 4
    - x 3 * y 1 * z 0 * t 4 * u 2
    - x 3 * y 1 * z 2 * t 0 * u 4
    + x 3 * y 1 * z 2 * t 4 * u 0
    + x 3 * y 1 * z 4 * t 0 * u 2
    - x 3 * y 1 * z 4 * t 2 * u 0
    - x 3 * y 2 * z 0 * t 1 * u 4
    + x 3 * y 2 * z 0 * t 4 * u 1
    + x 3 * y 2 * z 1 * t 0 * u 4
    - x 3 * y 2 * z 1 * t 4 * u 0
    - x 3 * y 2 * z 4 * t 0 * u 1
    + x 3 * y 2 * z 4 * t 1 * u 0
    + x 3 * y 4 * z 0 * t 1 * u 2
    - x 3 * y 4 * z 0 * t 2 * u 1
    - x 3 * y 4 * z 1 * t 0 * u 2
    + x 3 * y 4 * z 1 * t 2 * u 0
    + x 3 * y 4 * z 2 * t 0 * u 1
    - x 3 * y 4 * z 2 * t 1 * u 0
    + x 4 * y 0 * z 1 * t 2 * u 3
    - x 4 * y 0 * z 1 * t 3 * u 2
    - x 4 * y 0 * z 2 * t 1 * u 3
    + x 4 * y 0 * z 2 * t 3 * u 1
    + x 4 * y 0 * z 3 * t 1 * u 2
    - x 4 * y 0 * z 3 * t 2 * u 1
    - x 4 * y 1 * z 0 * t 2 * u 3
    + x 4 * y 1 * z 0 * t 3 * u 2
    + x 4 * y 1 * z 2 * t 0 * u 3
    - x 4 * y 1 * z 2 * t 3 * u 0
    - x 4 * y 1 * z 3 * t 0 * u 2
    + x 4 * y 1 * z 3 * t 2 * u 0
    + x 4 * y 2 * z 0 * t 1 * u 3
    - x 4 * y 2 * z 0 * t 3 * u 1
    - x 4 * y 2 * z 1 * t 0 * u 3
    + x 4 * y 2 * z 1 * t 3 * u 0
    + x 4 * y 2 * z 3 * t 0 * u 1
    - x 4 * y 2 * z 3 * t 1 * u 0
    - x 4 * y 3 * z 0 * t 1 * u 2
    + x 4 * y 3 * z 0 * t 2 * u 1
    + x 4 * y 3 * z 1 * t 0 * u 2
    - x 4 * y 3 * z 1 * t 2 * u 0
    - x 4 * y 3 * z 2 * t 0 * u 1
    + x 4 * y 3 * z 2 * t 1 * u 0

theorem nzV : ∀ i : Fin 16, ∃ r, vZ i r ≠ 0 := by decide

theorem orthExact :
    ∀ i j : Fin 16, i ≠ j →
      (clebschEdge i j ↔ dot5Z (vZ i) (vZ j) = 0) := by decide +kernel

theorem span6 :
    ∀ i1 i2 : Fin 16, i1 < i2 → ∀ i3 : Fin 16, i2 < i3 →
    ∀ i4 : Fin 16, i3 < i4 → ∀ i5 : Fin 16, i4 < i5 →
    ∀ i6 : Fin 16, i5 < i6 →
      det5Z (vZ i1) (vZ i2) (vZ i3) (vZ i4) (vZ i5) ≠ 0 ∨
      det5Z (vZ i1) (vZ i2) (vZ i3) (vZ i4) (vZ i6) ≠ 0 ∨
      det5Z (vZ i1) (vZ i2) (vZ i3) (vZ i5) (vZ i6) ≠ 0 ∨
      det5Z (vZ i1) (vZ i2) (vZ i4) (vZ i5) (vZ i6) ≠ 0 ∨
      det5Z (vZ i1) (vZ i3) (vZ i4) (vZ i5) (vZ i6) ≠ 0 ∨
      det5Z (vZ i2) (vZ i3) (vZ i4) (vZ i5) (vZ i6) ≠ 0 := by decide +kernel

lemma dot5_cast (x y : Fin 5 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot5Z x y : ℂ) := by
  simp only [dot5Z, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero]
  push_cast
  ring

lemma linInd_of_det5 {x y z t u : Fin 5 → ℤ} (hd : det5Z x y z t u ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 5 => (x r : ℂ)),
      (fun r : Fin 5 => (y r : ℂ)),
      (fun r : Fin 5 => (z r : ℂ)),
      (fun r : Fin 5 => (t r : ℂ)),
      (fun r : Fin 5 => (u r : ℂ))] := by
  let M : Matrix (Fin 5) (Fin 5) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ), (x 4 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ), (y 4 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ), (z 4 : ℂ);
       (t 0 : ℂ), (t 1 : ℂ), (t 2 : ℂ), (t 3 : ℂ), (t 4 : ℂ);
       (u 0 : ℂ), (u 1 : ℂ), (u 2 : ℂ), (u 3 : ℂ), (u 4 : ℂ)]
  have hdet : M.det = (det5Z x y z t u : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det5Z, Fin.sum_univ_succ,
      Fin.val_zero, Fin.zero_succAbove, Fin.val_succ, Fin.val_eq_zero,
      Fin.succ_succAbove_zero, Fin.succ_succAbove_one, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 5 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam :
      (fun i : Fin 5 => M i) =
        ![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ),
          fun r => (t r : ℂ), fun r => (u r : ℂ)] := by
    ext i r
    fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd_v (i j k l n : Fin 16)
    (hd : det5Z (vZ i) (vZ j) (vZ k) (vZ l) (vZ n) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k, v l, v n] := by
  have h := linInd_of_det5 hd
  convert h using 1
  ext s r
  fin_cases s <;> simp [v]

theorem proof :
    ∃ v : Fin 16 → Fin 5 → ℂ,
      (∀ i, v i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (clebschEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
      (∀ i1 i2 i3 i4 i5 i6 : Fin 16,
        i1 < i2 → i2 < i3 → i3 < i4 → i4 < i5 → i5 < i6 →
        LinearIndependent ℂ ![v i1, v i2, v i3, v i4, v i5] ∨
        LinearIndependent ℂ ![v i1, v i2, v i3, v i4, v i6] ∨
        LinearIndependent ℂ ![v i1, v i2, v i3, v i5, v i6] ∨
        LinearIndependent ℂ ![v i1, v i2, v i4, v i5, v i6] ∨
        LinearIndependent ℂ ![v i1, v i3, v i4, v i5, v i6] ∨
        LinearIndependent ℂ ![v i2, v i3, v i4, v i5, v i6]) := by
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr⟩ := nzV i
    apply hr
    have h := congr_fun hi r
    simpa [v] using h
  · intro i j hij
    have hdot :
        (∑ r, star (v i r) * v j r) = (dot5Z (vZ i) (vZ j) : ℂ) := by
      simpa [v] using dot5_cast (vZ i) (vZ j)
    constructor
    · intro he
      have hz : dot5Z (vZ i) (vZ j) = 0 := (orthExact i j hij).mp he
      rw [hdot]
      exact_mod_cast hz
    · intro hip
      have hz : dot5Z (vZ i) (vZ j) = 0 := by
        have := hdot.symm.trans hip
        exact_mod_cast this
      exact (orthExact i j hij).mpr hz
  · intro i1 i2 i3 i4 i5 i6 h12 h23 h34 h45 h56
    rcases span6 i1 i2 h12 i3 h23 i4 h34 i5 h45 i6 h56 with h | h | h | h | h | h
    · exact Or.inl (linInd_v i1 i2 i3 i4 i5 h)
    · exact Or.inr <| Or.inl (linInd_v i1 i2 i3 i4 i6 h)
    · exact Or.inr <| Or.inr <| Or.inl (linInd_v i1 i2 i3 i5 i6 h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (linInd_v i1 i2 i4 i5 i6 h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (linInd_v i1 i3 i4 i5 i6 h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (linInd_v i2 i3 i4 i5 i6 h)

end Submissions.SpanningOrthRep5Clebsch.Clebsch
