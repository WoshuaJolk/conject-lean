import Mathlib

namespace Submissions.MinUPB344.Petersen

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def uZ : Fin 10 → Fin 3 → ℤ
  | ⟨0, _⟩ => ![4, 1, 16]
  | ⟨1, _⟩ => ![4, 0, -1]
  | ⟨2, _⟩ => ![0, -1, 0]
  | ⟨3, _⟩ => ![-1, 0, 4]
  | ⟨4, _⟩ => ![-4, 32, -1]
  | ⟨5, _⟩ => ![1, -4, 0]
  | ⟨6, _⟩ => ![-1, 8, -4]
  | ⟨7, _⟩ => ![0, 0, -1]
  | ⟨8, _⟩ => ![4, 1, 1]
  | ⟨9, _⟩ => ![8, 1, 0]

def wZ : Fin 10 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![-1, 0, 2, 0]
  | ⟨1, _⟩ => ![-1, 0, -1, -1]
  | ⟨2, _⟩ => ![2, -1, 2, 0]
  | ⟨3, _⟩ => ![-6, -1, -3, -3]
  | ⟨4, _⟩ => ![1, -1, 0, -1]
  | ⟨5, _⟩ => ![-7, -6, 4, 3]
  | ⟨6, _⟩ => ![2, 6, 1, -7]
  | ⟨7, _⟩ => ![-1, -3, 1, 2]
  | ⟨8, _⟩ => ![10, 3, 5, 7]
  | ⟨9, _⟩ => ![1, -2, -2, 1]

def zZ : Fin 10 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![2, -4, 2, 1]
  | ⟨1, _⟩ => ![4, -4, 2, 1]
  | ⟨2, _⟩ => ![3, 0, -1, -4]
  | ⟨3, _⟩ => ![1, 1, -2, 4]
  | ⟨4, _⟩ => ![-10, 1, 6, -9]
  | ⟨5, _⟩ => ![8, 14, 11, 0]
  | ⟨6, _⟩ => ![-63, 36, 0, 74]
  | ⟨7, _⟩ => ![0, 37, 83, -18]
  | ⟨8, _⟩ => ![-3, -4, -1, -2]
  | ⟨9, _⟩ => ![-69, 11, 67, 48]

def u (i : Fin 10) : Fin 3 → ℂ := fun r => (uZ i r : ℂ)
def w (i : Fin 10) : Fin 4 → ℂ := fun r => (wZ i r : ℂ)
def z (i : Fin 10) : Fin 4 → ℂ := fun r => (zZ i r : ℂ)

def dot3Z (x y : Fin 3 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def det3Z (x y z : Fin 3 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

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

theorem nzU : ∀ i : Fin 10, ∃ r, uZ i r ≠ 0 := by decide

theorem nzW : ∀ i : Fin 10, ∃ r, wZ i r ≠ 0 := by decide

theorem nzZ : ∀ i : Fin 10, ∃ r, zZ i r ≠ 0 := by decide

theorem orthZ :
    ∀ i j : Fin 10, i ≠ j →
      dot3Z (uZ i) (uZ j) = 0 ∨
      dot4Z (wZ i) (wZ j) = 0 ∨
      dot4Z (zZ i) (zZ j) = 0 := by decide

theorem genU :
    ∀ i j k l : Fin 10, i < j → j < k → k < l →
      det3Z (uZ i) (uZ j) (uZ k) ≠ 0 ∨
      det3Z (uZ i) (uZ j) (uZ l) ≠ 0 ∨
      det3Z (uZ i) (uZ k) (uZ l) ≠ 0 ∨
      det3Z (uZ j) (uZ k) (uZ l) ≠ 0 := by decide

theorem genW :
    ∀ i j k l : Fin 10, i < j → j < k → k < l →
      det4Z (wZ i) (wZ j) (wZ k) (wZ l) ≠ 0 := by decide

theorem genZ :
    ∀ i j k l : Fin 10, i < j → j < k → k < l →
      det4Z (zZ i) (zZ j) (zZ k) (zZ l) ≠ 0 := by decide

lemma kill3 {x y z : Fin 3 → ℤ} {a : Fin 3 → ℂ}
    (hd : det3Z x y z ≠ 0)
    (hx : ∑ r, star ((x r : ℂ)) * a r = 0)
    (hy : ∑ r, star ((y r : ℂ)) * a r = 0)
    (hz : ∑ r, star ((z r : ℂ)) * a r = 0) : a = 0 := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ)]
  have hdet : M.det = (det3Z x y z : ℂ) := by
    simp [M, Matrix.det_fin_three, det3Z]
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact_mod_cast hd
  have hm : Matrix.mulVec M a = 0 := by
    funext i
    fin_cases i
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, star_intCast] using hx
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, star_intCast] using hy
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, star_intCast] using hz
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm

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
    rw [hdet]
    exact_mod_cast hd
  have hm : Matrix.mulVec M a = 0 := by
    funext i
    fin_cases i
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using hx
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using hy
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using hz
    · simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four, star_intCast] using ht
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 hm

lemma dot3_cast (x y : Fin 3 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot3Z x y : ℂ) := by
  simp [dot3Z, Fin.sum_univ_three, star_intCast]

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

theorem proof :
    ∃ u : Fin 10 → Fin 3 → ℂ,
    ∃ w : Fin 10 → Fin 4 → ℂ,
    ∃ z : Fin 10 → Fin 4 → ℂ,
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
      (∀ a : Fin 3 → ℂ, a ≠ 0 → ∀ b : Fin 4 → ℂ, b ≠ 0 →
        ∀ c : Fin 4 → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0) := by
  have hu0 : ∀ i : Fin 10, u i ≠ 0 := by
    intro i hi
    obtain ⟨r, hr⟩ := nzU i
    apply hr
    have h := congr_fun hi r
    simpa [u] using h
  have hw0 : ∀ i : Fin 10, w i ≠ 0 := by
    intro i hi
    obtain ⟨r, hr⟩ := nzW i
    apply hr
    have h := congr_fun hi r
    simpa [w] using h
  have hz0 : ∀ i : Fin 10, z i ≠ 0 := by
    intro i hi
    obtain ⟨r, hr⟩ := nzZ i
    apply hr
    have h := congr_fun hi r
    simpa [z] using h
  refine ⟨u, w, z, hu0, hw0, hz0, ?_, ?_⟩
  · intro i j hij
    rcases orthZ i j hij with hU | hW | hZ
    · have h : (∑ r, star (u i r) * u j r) = 0 := by
        rw [show (∑ r, star (u i r) * u j r) =
            (dot3Z (uZ i) (uZ j) : ℂ) by
          simpa [u] using dot3_cast (uZ i) (uZ j)]
        exact_mod_cast hU
      rw [h]
      simp
    · have h : (∑ r, star (w i r) * w j r) = 0 := by
        rw [show (∑ r, star (w i r) * w j r) =
            (dot4Z (wZ i) (wZ j) : ℂ) by
          simpa [w] using dot4_cast (wZ i) (wZ j)]
        exact_mod_cast hW
      rw [h]
      simp
    · have h : (∑ r, star (z i r) * z j r) = 0 := by
        rw [show (∑ r, star (z i r) * z j r) =
            (dot4Z (zZ i) (zZ j) : ℂ) by
          simpa [z] using dot4_cast (zZ i) (zZ j)]
        exact_mod_cast hZ
      rw [h]
      simp
  · intro a ha b hb c hc
    by_contra h
    push_neg at h
    let A : Finset (Fin 10) :=
      Finset.univ.filter (fun i => ∑ r, star (u i r) * a r = 0)
    let B : Finset (Fin 10) :=
      Finset.univ.filter (fun i => ∑ r, star (w i r) * b r = 0)
    let C : Finset (Fin 10) :=
      Finset.univ.filter (fun i => ∑ r, star (z i r) * c r = 0)
    have hcover : (Finset.univ : Finset (Fin 10)) ⊆ (A ∪ B) ∪ C := by
      intro i hi
      have hi0 := h i
      rcases mul_eq_zero.mp hi0 with hab | hC
      · rcases mul_eq_zero.mp hab with hA | hB
        · exact Finset.mem_union_left C
            (Finset.mem_union_left B (Finset.mem_filter.mpr ⟨hi, hA⟩))
        · exact Finset.mem_union_left C
            (Finset.mem_union_right A (Finset.mem_filter.mpr ⟨hi, hB⟩))
      · exact Finset.mem_union_right (A ∪ B)
          (Finset.mem_filter.mpr ⟨hi, hC⟩)
    have hcard : 10 ≤ A.card + B.card + C.card := by
      have hle : 10 ≤ ((A ∪ B) ∪ C).card := by
        simpa using (Finset.card_le_card hcover)
      have hab := Finset.card_union_le A B
      have habc := Finset.card_union_le (A ∪ B) C
      omega
    have hAcard : A.card ≤ 3 := by
      by_contra hA
      have h4 : 4 ≤ A.card := by omega
      obtain ⟨t, htA, htcard⟩ := Finset.exists_subset_card_eq h4
      let e : Fin 4 ≃o t := t.orderIsoOfFin htcard
      let i : Fin 10 := e 0
      let j : Fin 10 := e 1
      let k : Fin 10 := e 2
      let l : Fin 10 := e 3
      have hij : i < j := e.strictMono (by decide)
      have hjk : j < k := e.strictMono (by decide)
      have hkl : k < l := e.strictMono (by decide)
      have hiA : i ∈ A := htA (e 0).property
      have hjA : j ∈ A := htA (e 1).property
      have hkA : k ∈ A := htA (e 2).property
      have hlA : l ∈ A := htA (e 3).property
      have hia := (Finset.mem_filter.mp hiA).2
      have hja := (Finset.mem_filter.mp hjA).2
      have hka := (Finset.mem_filter.mp hkA).2
      have hla := (Finset.mem_filter.mp hlA).2
      have hia' : ∑ r, star ((uZ i r : ℂ)) * a r = 0 := by
        simpa [u] using hia
      have hja' : ∑ r, star ((uZ j r : ℂ)) * a r = 0 := by
        simpa [u] using hja
      have hka' : ∑ r, star ((uZ k r : ℂ)) * a r = 0 := by
        simpa [u] using hka
      have hla' : ∑ r, star ((uZ l r : ℂ)) * a r = 0 := by
        simpa [u] using hla
      rcases genU i j k l hij hjk hkl with hd | hd | hd | hd
      · exact ha (kill3 hd hia' hja' hka')
      · exact ha (kill3 hd hia' hja' hla')
      · exact ha (kill3 hd hia' hka' hla')
      · exact ha (kill3 hd hja' hka' hla')
    have hBcard : B.card ≤ 3 := by
      by_contra hB
      have h4 : 4 ≤ B.card := by omega
      obtain ⟨t, htB, htcard⟩ := Finset.exists_subset_card_eq h4
      let e : Fin 4 ≃o t := t.orderIsoOfFin htcard
      let i : Fin 10 := e 0
      let j : Fin 10 := e 1
      let k : Fin 10 := e 2
      let l : Fin 10 := e 3
      have hij : i < j := e.strictMono (by decide)
      have hjk : j < k := e.strictMono (by decide)
      have hkl : k < l := e.strictMono (by decide)
      have hiB : i ∈ B := htB (e 0).property
      have hjB : j ∈ B := htB (e 1).property
      have hkB : k ∈ B := htB (e 2).property
      have hlB : l ∈ B := htB (e 3).property
      have hib := (Finset.mem_filter.mp hiB).2
      have hjb := (Finset.mem_filter.mp hjB).2
      have hkb := (Finset.mem_filter.mp hkB).2
      have hlb := (Finset.mem_filter.mp hlB).2
      have hib' : ∑ r, star ((wZ i r : ℂ)) * b r = 0 := by
        simpa [w] using hib
      have hjb' : ∑ r, star ((wZ j r : ℂ)) * b r = 0 := by
        simpa [w] using hjb
      have hkb' : ∑ r, star ((wZ k r : ℂ)) * b r = 0 := by
        simpa [w] using hkb
      have hlb' : ∑ r, star ((wZ l r : ℂ)) * b r = 0 := by
        simpa [w] using hlb
      exact hb (kill4 (genW i j k l hij hjk hkl) hib' hjb' hkb' hlb')
    have hCcard : C.card ≤ 3 := by
      by_contra hC
      have h4 : 4 ≤ C.card := by omega
      obtain ⟨t, htC, htcard⟩ := Finset.exists_subset_card_eq h4
      let e : Fin 4 ≃o t := t.orderIsoOfFin htcard
      let i : Fin 10 := e 0
      let j : Fin 10 := e 1
      let k : Fin 10 := e 2
      let l : Fin 10 := e 3
      have hij : i < j := e.strictMono (by decide)
      have hjk : j < k := e.strictMono (by decide)
      have hkl : k < l := e.strictMono (by decide)
      have hiC : i ∈ C := htC (e 0).property
      have hjC : j ∈ C := htC (e 1).property
      have hkC : k ∈ C := htC (e 2).property
      have hlC : l ∈ C := htC (e 3).property
      have hic := (Finset.mem_filter.mp hiC).2
      have hjc := (Finset.mem_filter.mp hjC).2
      have hkc := (Finset.mem_filter.mp hkC).2
      have hlc := (Finset.mem_filter.mp hlC).2
      have hic' : ∑ r, star ((zZ i r : ℂ)) * c r = 0 := by
        simpa [z] using hic
      have hjc' : ∑ r, star ((zZ j r : ℂ)) * c r = 0 := by
        simpa [z] using hjc
      have hkc' : ∑ r, star ((zZ k r : ℂ)) * c r = 0 := by
        simpa [z] using hkc
      have hlc' : ∑ r, star ((zZ l r : ℂ)) * c r = 0 := by
        simpa [z] using hlc
      exact hc (kill4 (genZ i j k l hij hjk hkl) hic' hjc' hkc' hlc')
    omega

end Submissions.MinUPB344.Petersen
