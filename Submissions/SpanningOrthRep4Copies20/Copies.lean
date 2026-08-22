import Mathlib

namespace Submissions.SpanningOrthRep4Copies20.Copies

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

abbrev circDist (i j : Fin 10) : ℕ :=
  let d := (i.val + 10 - j.val) % 10
  min d (10 - d)

abbrev blk (i : Fin 20) : ℕ := i.val / 10

abbrev posn (i : Fin 20) : ℕ := i.val % 10

abbrev twoCircEdge (i j : Fin 20) : Prop :=
  blk i = blk j ∧
    (circDist ⟨posn i, Nat.mod_lt _ (by norm_num)⟩
        ⟨posn j, Nat.mod_lt _ (by norm_num)⟩ = 1 ∨
     circDist ⟨posn i, Nat.mod_lt _ (by norm_num)⟩
        ⟨posn j, Nat.mod_lt _ (by norm_num)⟩ = 2)

abbrev Rank4of5 (v : Fin 20 → Fin 4 → ℂ)
    (i j k l t : Fin 20) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

def vZ : Fin 20 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0],
  ![0, 2, -1, 0],
  ![0, 0, 0, 2],
  ![1, 1, 2, 0],
  ![2, -2, 0, 0],
  ![-2, -2, 2, 2],
  ![-2, -2, -2, -2],
  ![2, -2, 2, -2],
  ![0, -2, 0, 2],
  ![0, -1, -2, -1],
  ![16, -24, 8, 25],
  ![10, 24, -73, 40],
  ![35, 6, -2, -16],
  ![2, -29, -12, -5],
  ![14, -21, 46, 17],
  ![11, 3, 25, -73],
  ![-47, 51, 35, 7],
  ![-9, -19, 15, 3],
  ![11, 3, 12, -8],
  ![-25, 57, 46, 56]]

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def det3Z (x y z : Fin 4 → ℤ) (a b c : Fin 4) : ℤ :=
  x a * y b * z c + x b * y c * z a + x c * y a * z b
    - x a * y c * z b - x b * y a * z c - x c * y b * z a

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

theorem nz : ∀ i : Fin 20, ∃ r, vZ i r ≠ 0 := by decide

theorem orth :
    ∀ i j : Fin 20, i ≠ j →
      (twoCircEdge i j ↔ dot4Z (vZ i) (vZ j) = 0) := by decide

theorem gen3 :
    ∀ i j k : Fin 20, i < j → j < k →
      det3Z (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
      det3Z (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
      det3Z (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
      det3Z (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0 := by decide

theorem gen4of5_0 :
    ∀ j k l t : Fin 20, (0 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 0) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 0) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 0) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 0) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_1 :
    ∀ j k l t : Fin 20, (1 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 1) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 1) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 1) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 1) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_2 :
    ∀ j k l t : Fin 20, (2 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 2) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 2) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 2) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 2) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_3 :
    ∀ j k l t : Fin 20, (3 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 3) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 3) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 3) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 3) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_4 :
    ∀ j k l t : Fin 20, (4 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 4) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 4) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 4) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 4) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_5 :
    ∀ j k l t : Fin 20, (5 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 5) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 5) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 5) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 5) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_6 :
    ∀ j k l t : Fin 20, (6 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 6) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 6) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 6) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 6) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_7 :
    ∀ j k l t : Fin 20, (7 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 7) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 7) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 7) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 7) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_8 :
    ∀ j k l t : Fin 20, (8 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 8) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 8) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 8) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 8) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_9 :
    ∀ j k l t : Fin 20, (9 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 9) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 9) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 9) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 9) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_10 :
    ∀ j k l t : Fin 20, (10 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 10) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 10) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 10) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 10) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_11 :
    ∀ j k l t : Fin 20, (11 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 11) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 11) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 11) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 11) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_12 :
    ∀ j k l t : Fin 20, (12 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 12) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 12) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 12) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 12) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_13 :
    ∀ j k l t : Fin 20, (13 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 13) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 13) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 13) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 13) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_14 :
    ∀ j k l t : Fin 20, (14 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 14) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 14) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 14) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 14) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_15 :
    ∀ j k l t : Fin 20, (15 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 15) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 15) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 15) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 15) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_16 :
    ∀ j k l t : Fin 20, (16 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 16) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 16) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 16) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 16) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_17 :
    ∀ j k l t : Fin 20, (17 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 17) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 17) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 17) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 17) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_18 :
    ∀ j k l t : Fin 20, (18 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 18) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 18) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 18) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 18) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5_19 :
    ∀ j k l t : Fin 20, (19 : Fin 20) < j → j < k → k < l → l < t →
      det4Z (vZ 19) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ 19) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ 19) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ 19) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem gen4of5 :
    ∀ i j k l t : Fin 20, i < j → j < k → k < l → l < t →
      det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ i) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ i) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ i) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by
  intro i j k l t hij hjk hkl hlt
  fin_cases i
  · exact gen4of5_0 j k l t hij hjk hkl hlt
  · exact gen4of5_1 j k l t hij hjk hkl hlt
  · exact gen4of5_2 j k l t hij hjk hkl hlt
  · exact gen4of5_3 j k l t hij hjk hkl hlt
  · exact gen4of5_4 j k l t hij hjk hkl hlt
  · exact gen4of5_5 j k l t hij hjk hkl hlt
  · exact gen4of5_6 j k l t hij hjk hkl hlt
  · exact gen4of5_7 j k l t hij hjk hkl hlt
  · exact gen4of5_8 j k l t hij hjk hkl hlt
  · exact gen4of5_9 j k l t hij hjk hkl hlt
  · exact gen4of5_10 j k l t hij hjk hkl hlt
  · exact gen4of5_11 j k l t hij hjk hkl hlt
  · exact gen4of5_12 j k l t hij hjk hkl hlt
  · exact gen4of5_13 j k l t hij hjk hkl hlt
  · exact gen4of5_14 j k l t hij hjk hkl hlt
  · exact gen4of5_15 j k l t hij hjk hkl hlt
  · exact gen4of5_16 j k l t hij hjk hkl hlt
  · exact gen4of5_17 j k l t hij hjk hkl hlt
  · exact gen4of5_18 j k l t hij hjk hkl hlt
  · exact gen4of5_19 j k l t hij hjk hkl hlt

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

lemma linInd_of_det4 {x y z t : Fin 4 → ℤ}
    (hd : det4Z x y z t ≠ 0) :
    LinearIndependent ℂ ![
      (fun r => (x r : ℂ)), (fun r => (y r : ℂ)),
      (fun r => (z r : ℂ)), (fun r => (t r : ℂ))] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(x 0 : ℂ), (y 0 : ℂ), (z 0 : ℂ), (t 0 : ℂ);
       (x 1 : ℂ), (y 1 : ℂ), (z 1 : ℂ), (t 1 : ℂ);
       (x 2 : ℂ), (y 2 : ℂ), (z 2 : ℂ), (t 2 : ℂ);
       (x 3 : ℂ), (y 3 : ℂ), (z 3 : ℂ), (t 3 : ℂ)]
  have hdet : M.det = (det4Z x y z t : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det4Z, Fin.sum_univ_succ,
      Fin.val_zero, Fin.zero_succAbove, Fin.val_succ, Fin.val_eq_zero,
      Fin.succ_succAbove_zero, Fin.succ_succAbove_one, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact_mod_cast hd
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  have hm : M.mulVec g = 0 := by
    funext q
    fin_cases q
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm] using
        congrFun hsum 0
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm] using
        congrFun hsum 1
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm] using
        congrFun hsum 2
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm] using
        congrFun hsum 3
  have hg : g = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm
  simpa [hg]

lemma linInd_of_det3 {x y z : Fin 4 → ℤ} {a b c : Fin 4}
    (habc : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : det3Z x y z a b c ≠ 0) :
    LinearIndependent ℂ ![
      (fun r => (x r : ℂ)), (fun r => (y r : ℂ)),
      (fun r => (z r : ℂ))] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x a : ℂ), (y a : ℂ), (z a : ℂ);
       (x b : ℂ), (y b : ℂ), (z b : ℂ);
       (x c : ℂ), (y c : ℂ), (z c : ℂ)]
  have hdet : M.det = (det3Z x y z a b c : ℂ) := by
    simp [M, det3Z, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact_mod_cast hd
  have hm : M.mulVec g = 0 := by
    funext q
    fin_cases q
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm] using congrFun hsum a
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm] using congrFun hsum b
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm] using congrFun hsum c
  have hg : g = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm
  simpa [hg]

def v : Fin 20 → Fin 4 → ℂ := fun i r => (vZ i r : ℂ)

theorem proof : ∃ v : Fin 20 → Fin 4 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (twoCircEdge i j ↔
      (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i j k : Fin 20, i < j → j < k →
      LinearIndependent ℂ ![v i, v j, v k]) ∧
    (∀ i j k l t : Fin 20, i < j → j < k → k < l → l < t →
      Rank4of5 v i j k l t) := by
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro i hzero
    obtain ⟨r, hr⟩ := nz i
    exact hr (by
      have := congrFun hzero r
      simpa [v] using this)
  · intro i j hne
    rw [show v i = fun r => (vZ i r : ℂ) by rfl,
      show v j = fun r => (vZ j r : ℂ) by rfl]
    rw [dot4_cast]
    exact_mod_cast (orth i j hne)
  · intro i j k hij hjk
    rcases gen3 i j k hij hjk with h | h | h | h
    · exact linInd_of_det3 (by decide) (by decide) (by decide) h
    · exact linInd_of_det3 (by decide) (by decide) (by decide) h
    · exact linInd_of_det3 (by decide) (by decide) (by decide) h
    · exact linInd_of_det3 (by decide) (by decide) (by decide) h
  · intro i j k l t hij hjk hkl hlt
    rcases gen4of5 i j k l t hij hjk hkl hlt with h | h | h | h | h
    · exact Or.inl (linInd_of_det4 h)
    · exact Or.inr (Or.inl (linInd_of_det4 h))
    · exact Or.inr (Or.inr (Or.inl (linInd_of_det4 h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (linInd_of_det4 h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (linInd_of_det4 h))))

end Submissions.SpanningOrthRep4Copies20.Copies
