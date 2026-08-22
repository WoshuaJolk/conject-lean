import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

namespace Submissions.MinUPB445.Gauss

open GaussianInt

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

abbrev dims : Fin 3 → ℕ := fun j => if j.val < 2 then 4 else 5

/-- Ordinary quart factor: three integer orthogonal (quaternion) frames carrying the class
`C_12(3,6)` = three disjoint `K_4` on the cliques {v : v ≡ c (mod 3)}; general position. -/
def frameZ : Fin 12 → Fin 4 → ℤ := ![
  ![1, 0, 0, 1],
  ![1, 2, 3, 0],
  ![2, 3, 1, 1],
  ![0, 1, -1, 0],
  ![-2, 1, 0, 3],
  ![-3, 2, -1, 1],
  ![0, 1, 1, 0],
  ![-3, 0, 1, -2],
  ![-1, 1, 2, -3],
  ![-1, 0, 0, 1],
  ![0, -3, 2, 1],
  ![-1, -1, 3, 2]]

/-- `C^5` factor: integer vectors orthogonal on `C_12(4,5)` (four triangles at distance 4 plus
the distance-5 twelve-cycle), every five linearly independent. -/
def pentaZ : Fin 12 → Fin 5 → ℤ := ![
  ![2, 1, 0, 0, 1],
  ![1, 0, -2, -2, -1],
  ![-8, 13, 9, -1, -2],
  ![1, -1, 0, -1, 0],
  ![-10, 6, 23, -7, 14],
  ![0, 0, -1, 1, 0],
  ![-1, -1, 0, 1, -3],
  ![19, -25, 55, 44, -13],
  ![-1, -1, -2, 0, 3],
  ![-11, -6, -2, -2, -3],
  ![-1, 0, -1, -1, 0],
  ![-2, -3, -1, 1, 2]]

/-- Degenerate quart factor: Gaussian-integer vectors whose Hermitian orthogonality graph is
exactly the squared cycle `C_12(1,2)`, with no five in a common hyperplane. -/
def cZ : Fin 12 → Fin 4 → GaussianInt := ![
  ![⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩],
  ![⟨1, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨2, 0⟩],
  ![⟨-18, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, 0⟩],
  ![⟨1, 0⟩, ⟨-6, 0⟩, ⟨12, 0⟩, ⟨6, 0⟩],
  ![⟨-36, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩],
  ![⟨0, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
  ![⟨1, 0⟩, ⟨-9, 0⟩, ⟨18, 0⟩, ⟨-9, 0⟩],
  ![⟨-396, 0⟩, ⟨1129, 0⟩, ⟨-2258, 0⟩, ⟨-5689, 0⟩],
  ![⟨42165648, -1162980⟩, ⟨196791374, -33022126⟩, ⟨95216531, -16423378⟩, ⟨-1673240, 46150⟩],
  ![⟨222366495, -218304002⟩, ⟨-23676696, 25950370⟩, ⟨-33944760, 54365392⟩, ⟨-6704316, -1232326⟩],
  ![⟨83070, -3011832⟩, ⟨4319171, 10147931⟩, ⟨-8666032, -19291918⟩, ⟨8652187, 19793890⟩]]

/-- Componentwise Gaussian conjugates of `cZ` (for the hyperplane certificates). -/
def sZ : Fin 12 → Fin 4 → GaussianInt := fun i r => star (cZ i r)

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def dot5Z (x y : Fin 5 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4

/-- Hermitian Gaussian pairing (conjugate-linear in the first slot). -/
def gdotG (x y : Fin 4 → GaussianInt) : GaussianInt :=
  star (x 0) * y 0 + star (x 1) * y 1 + star (x 2) * y 2 + star (x 3) * y 3

def det4Z (x y z t : Fin 4 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

def det4G (x y z t : Fin 4 → GaussianInt) : GaussianInt :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

def det4C (x y z t : Fin 4 → ℂ) : ℂ :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

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

theorem nzFrame : ∀ i : Fin 12, ∃ r, frameZ i r ≠ 0 := by decide +kernel

theorem nzPenta : ∀ i : Fin 12, ∃ r, pentaZ i r ≠ 0 := by decide +kernel

theorem nzG : ∀ i : Fin 12, ∃ r, cZ i r ≠ 0 := by decide +kernel

/-- Every pair of distinct states is orthogonal in some factor: the classes `C_12(3,6)`,
`C_12(1,2)` and `C_12(4,5)` partition the distance classes of `Z_12`. -/
theorem orthZ :
    ∀ i i' : Fin 12, i ≠ i' →
      dot4Z (frameZ i) (frameZ i') = 0 ∨
      gdotG (cZ i) (cZ i') = 0 ∨
      dot5Z (pentaZ i) (pentaZ i') = 0 := by decide +kernel

/-- The frame factor is in general position. -/
theorem genFrame :
    ∀ i j l n : Fin 12, i < j → j < l → l < n →
      det4Z (frameZ i) (frameZ j) (frameZ l) (frameZ n) ≠ 0 := by decide +kernel

/-- The `C^5` factor is in general position. -/
theorem genPenta :
    ∀ i j l n p : Fin 12, i < j → j < l → l < n → n < p →
      det5Z (pentaZ i) (pentaZ j) (pentaZ l) (pentaZ n) (pentaZ p) ≠ 0 := by decide +kernel

/-- No five of the degenerate factor's vectors lie in a common hyperplane: every five contain
four whose conjugate matrix has nonzero determinant. -/
theorem span5G :
    ∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
      det4G (sZ i) (sZ j) (sZ k) (sZ l) ≠ 0 ∨
      det4G (sZ i) (sZ j) (sZ k) (sZ t) ≠ 0 ∨
      det4G (sZ i) (sZ j) (sZ l) (sZ t) ≠ 0 ∨
      det4G (sZ i) (sZ k) (sZ l) (sZ t) ≠ 0 ∨
      det4G (sZ j) (sZ k) (sZ l) (sZ t) ≠ 0 := by decide +kernel

lemma kill4 {x y z t : Fin 4 → ℤ} {a : Fin 4 → ℂ}
    (hd : det4Z x y z t ≠ 0)
    (hx : ∑ r, star ((x r : ℂ)) * a r = 0)
    (hy : ∑ r, star ((y r : ℂ)) * a r = 0)
    (hz : ∑ r, star ((z r : ℂ)) * a r = 0)
    (ht : ∑ r, star ((t r : ℂ)) * a r = 0) : a = 0 := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ);
       (t 0 : ℂ), (t 1 : ℂ), (t 2 : ℂ), (t 3 : ℂ)]
  have hdet : M.det = (det4Z x y z t : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det4Z, Fin.sum_univ_succ,
      Fin.val_zero, Fin.zero_succAbove, Fin.val_succ, Fin.val_eq_zero,
      Fin.succ_succAbove_zero, Fin.succ_succAbove_one, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]; exact_mod_cast hd
  have hm : Matrix.mulVec M a = 0 := by
    funext i
    fin_cases i
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using hx
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using hy
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using hz
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using ht
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm

lemma det4G_cast (x y z t : Fin 4 → GaussianInt) :
    det4C (fun r => ((x r : ℂ))) (fun r => ((y r : ℂ)))
        (fun r => ((z r : ℂ))) (fun r => ((t r : ℂ)))
      = ((det4G x y z t : GaussianInt) : ℂ) := by
  simp only [det4C, det4G, ← GaussianInt.toComplex_mul, ← GaussianInt.toComplex_add,
    ← GaussianInt.toComplex_sub]

lemma starcast (w : GaussianInt) :
    star ((w : ℂ)) = ((star w : GaussianInt) : ℂ) := by
  rw [Complex.star_def, GaussianInt.toComplex_star]

lemma kill4G {x y z t : Fin 4 → GaussianInt} {a : Fin 4 → ℂ}
    (hd : det4G (fun r => star (x r)) (fun r => star (y r))
        (fun r => star (z r)) (fun r => star (t r)) ≠ 0)
    (hx : ∑ r, star ((x r : ℂ)) * a r = 0)
    (hy : ∑ r, star ((y r : ℂ)) * a r = 0)
    (hz : ∑ r, star ((z r : ℂ)) * a r = 0)
    (ht : ∑ r, star ((t r : ℂ)) * a r = 0) : a = 0 := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![((star (x 0) : GaussianInt) : ℂ), ((star (x 1) : GaussianInt) : ℂ),
       ((star (x 2) : GaussianInt) : ℂ), ((star (x 3) : GaussianInt) : ℂ);
       ((star (y 0) : GaussianInt) : ℂ), ((star (y 1) : GaussianInt) : ℂ),
       ((star (y 2) : GaussianInt) : ℂ), ((star (y 3) : GaussianInt) : ℂ);
       ((star (z 0) : GaussianInt) : ℂ), ((star (z 1) : GaussianInt) : ℂ),
       ((star (z 2) : GaussianInt) : ℂ), ((star (z 3) : GaussianInt) : ℂ);
       ((star (t 0) : GaussianInt) : ℂ), ((star (t 1) : GaussianInt) : ℂ),
       ((star (t 2) : GaussianInt) : ℂ), ((star (t 3) : GaussianInt) : ℂ)]
  have hdetC : M.det = det4C (fun r => ((star (x r) : GaussianInt) : ℂ))
      (fun r => ((star (y r) : GaussianInt) : ℂ))
      (fun r => ((star (z r) : GaussianInt) : ℂ))
      (fun r => ((star (t r) : GaussianInt) : ℂ)) := by
    simp [M, Matrix.det_succ_row_zero, det4C, Fin.sum_univ_succ,
      Fin.val_zero, Fin.zero_succAbove, Fin.val_succ, Fin.val_eq_zero,
      Fin.succ_succAbove_zero, Fin.succ_succAbove_one, Fin.succAbove]
    ring
  have hdet : M.det = ((det4G (fun r => star (x r)) (fun r => star (y r))
      (fun r => star (z r)) (fun r => star (t r)) : GaussianInt) : ℂ) := by
    rw [hdetC, det4G_cast]
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact fun h => hd (GaussianInt.toComplex_eq_zero.mp h)
  have hm : Matrix.mulVec M a = 0 := by
    funext i
    fin_cases i
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ← starcast] using hx
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ← starcast] using hy
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ← starcast] using hz
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ← starcast] using ht
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

lemma gdot_cast (x y : Fin 4 → GaussianInt) :
    (∑ r, star ((x r : ℂ)) * ((y r : ℂ))) = ((gdotG x y : GaussianInt) : ℂ) := by
  simp only [gdotG, Fin.sum_univ_four, starcast, ← GaussianInt.toComplex_mul,
    ← GaussianInt.toComplex_add]

lemma dot5_cast (x y : Fin 5 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot5Z x y : ℂ) := by
  simp only [dot5Z, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero]
  push_cast
  ring

lemma kill5 {x y z t u : Fin 5 → ℤ} {a : Fin 5 → ℂ}
    (hd : det5Z x y z t u ≠ 0)
    (hx : ∑ r, star ((x r : ℂ)) * a r = 0)
    (hy : ∑ r, star ((y r : ℂ)) * a r = 0)
    (hz : ∑ r, star ((z r : ℂ)) * a r = 0)
    (ht : ∑ r, star ((t r : ℂ)) * a r = 0)
    (hu : ∑ r, star ((u r : ℂ)) * a r = 0) : a = 0 := by
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
    rw [hdet]; exact_mod_cast hd
  have hm : Matrix.mulVec M a = 0 := by
    funext i
    fin_cases i
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero] using hx
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero] using hy
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero] using hz
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero] using ht
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, add_zero] using hu
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm

lemma killFrame :
    ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 12),
        (∀ i ∈ S, ∑ r, star ((frameZ i r : ℂ)) * a r = 0) → S.card ≤ 3 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 4 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 4 ≃o T := T.orderIsoOfFin hTcard
  have hdet := genFrame (e 0).1 (e 1).1 (e 2).1 (e 3).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (e.strictMono (by decide))
  exact ha (kill4 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property))
    (hS (e 2).1 (hT (e 2).property))
    (hS (e 3).1 (hT (e 3).property)))

lemma killG :
    ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 12),
        (∀ i ∈ S, ∑ r, star ((cZ i r : ℂ)) * a r = 0) → S.card ≤ 4 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 5 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 5 ≃o T := T.orderIsoOfFin hTcard
  have hkill (i : Fin 5) :
      ∑ r, star ((cZ (e i).1 r : ℂ)) * a r = 0 :=
    hS (e i).1 (hT (e i).property)
  have hspan := span5G (e 0).1 (e 1).1 (e 2).1 (e 3).1 (e 4).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (e.strictMono (by decide)) (e.strictMono (by decide))
  rcases hspan with h | h | h | h | h
  · exact ha (kill4G h (hkill 0) (hkill 1) (hkill 2) (hkill 3))
  · exact ha (kill4G h (hkill 0) (hkill 1) (hkill 2) (hkill 4))
  · exact ha (kill4G h (hkill 0) (hkill 1) (hkill 3) (hkill 4))
  · exact ha (kill4G h (hkill 0) (hkill 2) (hkill 3) (hkill 4))
  · exact ha (kill4G h (hkill 1) (hkill 2) (hkill 3) (hkill 4))

lemma killPenta :
    ∀ a : Fin 5 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 12),
        (∀ i ∈ S, ∑ r, star ((pentaZ i r : ℂ)) * a r = 0) → S.card ≤ 4 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 5 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 5 ≃o T := T.orderIsoOfFin hTcard
  have hdet := genPenta (e 0).1 (e 1).1 (e 2).1 (e 3).1 (e 4).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (e.strictMono (by decide)) (e.strictMono (by decide))
  exact ha (kill5 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property))
    (hS (e 2).1 (hT (e 2).property))
    (hS (e 3).1 (hT (e 3).property))
    (hS (e 4).1 (hT (e 4).property)))

def v : Fin 12 → (j : Fin 3) → Fin (dims j) → ℂ :=
  fun i =>
    Fin.cases
      (fun r => ((frameZ i r : ℤ) : ℂ))
      (fun j =>
        Fin.cases
          (fun r => ((cZ i r : GaussianInt) : ℂ))
          (fun _ r => ((pentaZ i r : ℤ) : ℂ))
          j)

@[simp] theorem v_zero (i : Fin 12) :
    v i 0 = fun r => ((frameZ i r : ℤ) : ℂ) := rfl

@[simp] theorem v_one (i : Fin 12) :
    v i 1 = fun r => ((cZ i r : GaussianInt) : ℂ) := rfl

@[simp] theorem v_penta (i : Fin 12) (k : Fin 1) :
    v i (Fin.succ (Fin.succ k)) = fun r => ((pentaZ i r : ℤ) : ℂ) := rfl

/-- Killing numbers: 3 for the general-position frame factor, 4 for the degenerate
`C_12(1,2)` factor, 4 for the general-position `C^5` factor. Sum 11 < 12. -/
def killing : Fin 3 → ℕ := fun j => if j.val = 0 then 3 else if j.val = 1 then 4 else 4

theorem budget :
    ∀ p m : ℕ, ∀ d : Fin p → ℕ, ∀ c : Fin p → ℕ,
      ∀ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
      (∑ j, c j) < m →
      (∀ j : Fin p, ∀ a : Fin (d j) → ℂ, a ≠ 0 →
        ∀ S : Finset (Fin m), (∀ i ∈ S, (∑ r, star (v i j r) * a r) = 0) → S.card ≤ c j) →
      ∀ a : (j : Fin p) → Fin (d j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0 := by
  intro p m d c v hbudget hkill a ha
  by_contra hsurvivor
  push Not at hsurvivor
  choose f hf using hsurvivor
  let S : Fin p → Finset (Fin m) :=
    fun j => Finset.univ.filter (fun i => f i = j)
  have hScap : ∀ j, (S j).card ≤ c j := by
    intro j
    apply hkill j (a j) (ha j)
    intro i hi
    have hfi : f i = j := (Finset.mem_filter.mp hi).2
    rw [← hfi]
    exact hf i
  have hcard : m = ∑ j, (S j).card := by
    have h :=
      Finset.card_eq_sum_card_fiberwise
        (f := f)
        (s := (Finset.univ : Finset (Fin m)))
        (t := (Finset.univ : Finset (Fin p)))
        (fun _ _ => Finset.mem_univ _)
    simpa [S] using h
  have hle : m ≤ ∑ j, c j := by
    calc
      m = ∑ j, (S j).card := hcard
      _ ≤ ∑ j, c j := Finset.sum_le_sum (fun j _ => hScap j)
  exact (Nat.not_lt_of_ge hle) hbudget

theorem proof :
    ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
      ∃ w : Fin m → (j : Fin 3) → Fin (dims j) → ℂ,
        (∀ i j, w i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (w i j r) * w i' j r) = 0) ∧
        (∀ a : (j : Fin 3) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (w i j r) * a j r) ≠ 0) := by
  refine ⟨12, by decide, ?_⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · obtain ⟨r, hr⟩ := nzFrame i
      intro h
      exact hr (by
        have hz := congrFun h r
        simpa using hz)
    · refine Fin.cases ?_ (fun k => ?_) k
      · obtain ⟨r, hr⟩ := nzG i
        intro h
        have hz := congrFun h r
        change ((cZ i r : GaussianInt) : ℂ) = 0 at hz
        exact hr (GaussianInt.toComplex_eq_zero.mp hz)
      · obtain ⟨r, hr⟩ := nzPenta i
        intro h
        have hz := congrFun h r
        change ((pentaZ i r : ℤ) : ℂ) = 0 at hz
        exact hr (by exact_mod_cast hz)
  · intro i i' hne
    rcases orthZ i i' hne with hF | hG | hP
    · refine ⟨0, ?_⟩
      rw [v_zero, v_zero]
      calc
        (∑ r, star ((frameZ i r : ℂ)) * (frameZ i' r : ℂ)) =
            (dot4Z (frameZ i) (frameZ i') : ℂ) := dot4_cast _ _
        _ = 0 := by exact_mod_cast hF
    · refine ⟨1, ?_⟩
      rw [v_one, v_one]
      calc
        (∑ r, star ((cZ i r : ℂ)) * ((cZ i' r : ℂ))) =
            ((gdotG (cZ i) (cZ i') : GaussianInt) : ℂ) := gdot_cast _ _
        _ = 0 := by rw [hG]; exact GaussianInt.toComplex_zero
    · refine ⟨2, ?_⟩
      have h2 : (2 : Fin 3) = Fin.succ (Fin.succ (0 : Fin 1)) := rfl
      rw [h2, v_penta, v_penta]
      calc
        (∑ r, star ((pentaZ i r : ℂ)) * (pentaZ i' r : ℂ)) =
            (dot5Z (pentaZ i) (pentaZ i') : ℂ) := dot5_cast _ _
        _ = 0 := by exact_mod_cast hP
  · intro a ha
    have hbudget : (∑ j, killing j) < 12 := by decide +kernel
    have hkill :
        ∀ j : Fin 3, ∀ b : Fin (dims j) → ℂ, b ≠ 0 →
          ∀ S : Finset (Fin 12),
            (∀ i ∈ S, (∑ r, star (v i j r) * b r) = 0) →
              S.card ≤ killing j := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro b hb S hS
        have hk := killFrame b hb S (by
          intro i hi
          have hh := hS i hi
          rw [v_zero] at hh
          exact hh)
        simpa [killing] using hk
      · refine Fin.cases ?_ (fun k => ?_) k
        · intro b hb S hS
          have hk := killG b hb S (by
            intro i hi
            have hh := hS i hi
            change (∑ r, star (v i 1 r) * b r) = 0 at hh
            rw [v_one] at hh
            exact hh)
          simpa [killing] using hk
        · intro b hb S hS
          have hk := killPenta b hb S (by
            intro i hi
            have hh := hS i hi
            rw [v_penta] at hh
            exact hh)
          simpa [killing] using hk
    exact budget 3 12 dims killing v hbudget hkill a ha

end Submissions.MinUPB445.Gauss
