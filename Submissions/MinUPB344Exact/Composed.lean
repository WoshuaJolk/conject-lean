import Mathlib

namespace Submissions.MinUPB344Exact.Composed

namespace Upper

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

theorem upperProof :
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


end Upper

namespace Lower

set_option maxRecDepth 40000
set_option maxHeartbeats 10000000

open Finset

def ip {d : ℕ} (x y : Fin d → ℂ) : ℂ := ∑ r, star (x r) * y r

lemma ip_conj {d : ℕ} (x y : Fin d → ℂ) : star (ip x y) = ip y x := by
  simp [ip, star_sum, mul_comm]

lemma ip_eq_zero_comm {d : ℕ} {x y : Fin d → ℂ} : ip x y = 0 ↔ ip y x = 0 := by
  constructor <;> intro h
  · rw [← ip_conj, h, star_zero]
  · rw [← ip_conj, h, star_zero]

lemma ip_self_ne_zero {d : ℕ} {x : Fin d → ℂ} (hx : x ≠ 0) : ip x x ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r, x r ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have key : ∀ r : Fin d, star (x r) * x r = ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have h := RCLike.conj_mul (K := ℂ) (x r)
    push_cast
    simpa using h
  have hsum : ip x x = ((∑ r, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  rw [hsum]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => sq_nonneg ‖x r‖)).1 hzero
  have hn : ‖x r₀‖ = 0 := by
    have h2 := hall r₀ (Finset.mem_univ r₀)
    nlinarith [norm_nonneg (x r₀)]
  exact hr₀ (norm_eq_zero.1 hn)

def ipMap {d m : ℕ} (z : Fin m → Fin d → ℂ) (T : Finset (Fin m)) :
    (Fin d → ℂ) →ₗ[ℂ] (T → ℂ) where
  toFun c := fun l => ip (z l.1) c
  map_add' c c' := by
    funext l
    simp [ip, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext l
    simp [ip, Finset.mul_sum, mul_left_comm]

lemma exists_kernel_vec {d m : ℕ} (z : Fin m → Fin d → ℂ) (T : Finset (Fin m))
    (hcard : T.card < d) :
    ∃ c : Fin d → ℂ, c ≠ 0 ∧ ∀ l ∈ T, ip (z l) c = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (ipMap z T) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hne
    obtain ⟨l, hlT, hl⟩ := hcon c hne
    have hzero : (ipMap z T) c ⟨l, hlT⟩ = 0 := by
      rw [LinearMap.mem_ker] at hc
      rw [hc]
      rfl
    exact hl hzero
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
  omega

lemma even_card_of_involutive {α : Type*} [DecidableEq α] (f : α → α)
    (hff : ∀ x, f (f x) = x) :
    ∀ s : Finset α, (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f x ≠ x) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hcl hneS
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hfa : f a ∈ s := hcl a ha
      have hfa' : f a ∈ s.erase a := Finset.mem_erase.2 ⟨hneS a ha, hfa⟩
      set t := (s.erase a).erase (f a) with ht
      have hts : t ⊆ s :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hat : a ∉ t := by
        simp [ht, Finset.mem_erase]
      have hsub : t ⊂ s := ⟨hts, fun h => hat (h ha)⟩
      have hclt : ∀ x ∈ t, f x ∈ t := by
        intro x hx
        rw [ht, Finset.mem_erase, Finset.mem_erase] at hx
        obtain ⟨hxfa, hxa, hxs⟩ := hx
        rw [ht, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hcl x hxs⟩
        · intro h
          exact hxa (by rw [← hff x, h, hff a])
        · intro h
          exact hxfa (by rw [← hff x, h])
      have hnet : ∀ x ∈ t, f x ≠ x := by
        intro x hx
        exact hneS x (hts hx)
      have hev := ih t hsub hclt hnet
      have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      have h2 : t.card = (s.erase a).card - 1 := Finset.card_erase_of_mem hfa'
      have hs1 : 1 ≤ s.card := Finset.card_pos.2 ⟨a, ha⟩
      have hs2 : 1 ≤ (s.erase a).card := Finset.card_pos.2 ⟨f a, hfa'⟩
      have : s.card = t.card + 2 := by omega
      rw [this]
      exact hev.add (even_two)

theorem lowerProof :
    ∀ m : ℕ, m ≤ 9 →
    ¬ ∃ u : Fin m → Fin 3 → ℂ,
      ∃ w : Fin m → Fin 4 → ℂ,
      ∃ z : Fin m → Fin 4 → ℂ,
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
  intro m hm
  rintro ⟨u, w, z, hu, hw, hz, horth, hunext⟩
  classical
  by_cases hm8 : m ≤ 8
  · let T1 : Finset (Fin m) := Finset.univ.filter (fun i => i.val < 2)
    let T2 : Finset (Fin m) := Finset.univ.filter (fun i => 2 ≤ i.val ∧ i.val < 5)
    let T3 : Finset (Fin m) := Finset.univ.filter (fun i => 5 ≤ i.val)
    have hT1 : T1.card ≤ 2 := by
      apply Finset.card_le_card_of_injOn (s := T1) (t := Finset.range 2)
        (fun i : Fin m => i.val)
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi |>.2)
      · intro a ha b hb hab
        exact Fin.ext hab
    have hT2 : T2.card ≤ 3 := by
      apply Finset.card_le_card_of_injOn (s := T2) (t := Finset.Icc 2 4)
        (fun i : Fin m => i.val)
      · intro i hi
        have hh := Finset.mem_filter.mp hi |>.2
        exact Finset.mem_Icc.mpr ⟨hh.1, Nat.le_of_lt_succ hh.2⟩
      · intro a ha b hb hab
        exact Fin.ext hab
    have hT3 : T3.card ≤ 3 := by
      apply Finset.card_le_card_of_injOn (s := T3) (t := Finset.Icc 5 7)
        (fun i : Fin m => i.val)
      · intro i hi
        have hh := Finset.mem_filter.mp hi |>.2
        have hil : i.val < m := i.isLt
        have hil8 : i.val < 8 := lt_of_lt_of_le hil hm8
        have hi7 : i.val ≤ 7 := by omega
        exact Finset.mem_Icc.mpr ⟨hh, hi7⟩
      · intro a ha b hb hab
        exact Fin.ext hab
    obtain ⟨a, ha0, ha⟩ := exists_kernel_vec u T1 (by omega)
    obtain ⟨b, hb0, hb⟩ := exists_kernel_vec w T2 (by omega)
    obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z T3 (by omega)
    obtain ⟨i, hi⟩ := hunext a ha0 b hb0 c hc0
    have hparts : i ∈ T1 ∨ i ∈ T2 ∨ i ∈ T3 := by
      by_cases h1 : i.val < 2
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩)
      · by_cases h2 : i.val < 5
        · exact Or.inr (Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, by omega⟩))
        · exact Or.inr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, by omega⟩))
    rcases hparts with hi1 | hi2 | hi3
    · exact hi (by
        change ip (u i) a * ip (w i) b * ip (z i) c = 0
        rw [ha i hi1]
        simp)
    · exact hi (by
        change ip (u i) a * ip (w i) b * ip (z i) c = 0
        rw [hb i hi2]
        simp)
    · exact hi (by
        change ip (u i) a * ip (w i) b * ip (z i) c = 0
        rw [hc i hi3]
        simp)
  · have hm9 : m = 9 := by omega
    subst m
    have hAcard : ∀ a : Fin 3 → ℂ, a ≠ 0 →
        (Finset.univ.filter (fun l => ip (u l) a = 0)).card ≤ 2 := by
      intro a ha
      by_contra hgt
      let A := Finset.univ.filter (fun l => ip (u l) a = 0)
      let R := Finset.univ \ A
      have hA3 : 3 ≤ A.card := by
        simpa [A] using
          (show 3 ≤ (Finset.univ.filter (fun l => ip (u l) a = 0)).card by omega)
      have hRle : R.card ≤ 6 := by
        have hAR : A.card + R.card = 9 := by
          change (Finset.univ.filter (fun l => ip (u l) a = 0)).card +
              (Finset.univ \ Finset.univ.filter (fun l => ip (u l) a = 0)).card = 9
          rw [Finset.card_sdiff,
            Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
          have hAle : (Finset.univ.filter (fun l => ip (u l) a = 0)).card ≤ 9 := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          simp
          omega
        omega
      obtain ⟨S, hSR, hScard, hRS⟩ : ∃ S : Finset (Fin 9), S ⊆ R ∧
          S.card ≤ 3 ∧ (R \ S).card ≤ 3 := by
        by_cases h3 : 3 ≤ R.card
        · obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq h3
          refine ⟨S, hSR, by omega, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSR]
          omega
        · refine ⟨∅, by simp, by simp, ?_⟩
          simp
          omega
      obtain ⟨b, hb0, hb⟩ := exists_kernel_vec w S (by omega)
      obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z (R \ S) (by omega)
      obtain ⟨i, hi⟩ := hunext a ha b hb0 c hc0
      have hkill : ip (u i) a = 0 ∨ ip (w i) b = 0 ∨ ip (z i) c = 0 := by
        by_cases hiA : i ∈ A
        · exact Or.inl (Finset.mem_filter.mp hiA).2
        · have hiR : i ∈ R := by
            change i ∈ Finset.univ \ A
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiA⟩
          by_cases hiS : i ∈ S
          · exact Or.inr (Or.inl (hb i hiS))
          · exact Or.inr (Or.inr (hc i (Finset.mem_sdiff.mpr ⟨hiR, hiS⟩)))
      rcases hkill with hkill | hkill | hkill
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
    have hBcard : ∀ b : Fin 4 → ℂ, b ≠ 0 →
        (Finset.univ.filter (fun l => ip (w l) b = 0)).card ≤ 3 := by
      intro b hb
      by_contra hgt
      let B := Finset.univ.filter (fun l => ip (w l) b = 0)
      let R := Finset.univ \ B
      have hB4 : 4 ≤ B.card := by
        simpa [B] using
          (show 4 ≤ (Finset.univ.filter (fun l => ip (w l) b = 0)).card by omega)
      have hRle : R.card ≤ 5 := by
        have hBR : B.card + R.card = 9 := by
          change (Finset.univ.filter (fun l => ip (w l) b = 0)).card +
              (Finset.univ \ Finset.univ.filter (fun l => ip (w l) b = 0)).card = 9
          rw [Finset.card_sdiff,
            Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
          have hBle : (Finset.univ.filter (fun l => ip (w l) b = 0)).card ≤ 9 := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          simp
          omega
        omega
      obtain ⟨S, hSR, hScard, hRS⟩ : ∃ S : Finset (Fin 9), S ⊆ R ∧
          S.card ≤ 2 ∧ (R \ S).card ≤ 3 := by
        by_cases h2 : 2 ≤ R.card
        · obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq h2
          refine ⟨S, hSR, by omega, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSR]
          omega
        · refine ⟨∅, by simp, by simp, ?_⟩
          simp
          omega
      obtain ⟨a, ha0, ha⟩ := exists_kernel_vec u S (by omega)
      obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z (R \ S) (by omega)
      obtain ⟨i, hi⟩ := hunext a ha0 b hb c hc0
      have hkill : ip (w i) b = 0 ∨ ip (u i) a = 0 ∨ ip (z i) c = 0 := by
        by_cases hiB : i ∈ B
        · exact Or.inl (Finset.mem_filter.mp hiB).2
        · have hiR : i ∈ R := by
            change i ∈ Finset.univ \ B
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiB⟩
          by_cases hiS : i ∈ S
          · exact Or.inr (Or.inl (ha i hiS))
          · exact Or.inr (Or.inr (hc i (Finset.mem_sdiff.mpr ⟨hiR, hiS⟩)))
      rcases hkill with hkill | hkill | hkill
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
    have hCcard : ∀ c : Fin 4 → ℂ, c ≠ 0 →
        (Finset.univ.filter (fun l => ip (z l) c = 0)).card ≤ 3 := by
      intro c hc
      by_contra hgt
      let C := Finset.univ.filter (fun l => ip (z l) c = 0)
      let R := Finset.univ \ C
      have hC4 : 4 ≤ C.card := by
        simpa [C] using
          (show 4 ≤ (Finset.univ.filter (fun l => ip (z l) c = 0)).card by omega)
      have hRle : R.card ≤ 5 := by
        have hCR : C.card + R.card = 9 := by
          change (Finset.univ.filter (fun l => ip (z l) c = 0)).card +
              (Finset.univ \ Finset.univ.filter (fun l => ip (z l) c = 0)).card = 9
          rw [Finset.card_sdiff,
            Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
          have hCle : (Finset.univ.filter (fun l => ip (z l) c = 0)).card ≤ 9 := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          simp
          omega
        omega
      obtain ⟨S, hSR, hScard, hRS⟩ : ∃ S : Finset (Fin 9), S ⊆ R ∧
          S.card ≤ 2 ∧ (R \ S).card ≤ 3 := by
        by_cases h2 : 2 ≤ R.card
        · obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq h2
          refine ⟨S, hSR, by omega, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSR]
          omega
        · refine ⟨∅, by simp, by simp, ?_⟩
          simp
          omega
      obtain ⟨a, ha0, ha⟩ := exists_kernel_vec u S (by omega)
      obtain ⟨b, hb0, hb⟩ := exists_kernel_vec w (R \ S) (by omega)
      obtain ⟨i, hi⟩ := hunext a ha0 b hb0 c hc
      have hkill : ip (z i) c = 0 ∨ ip (u i) a = 0 ∨ ip (w i) b = 0 := by
        by_cases hiC : i ∈ C
        · exact Or.inl (Finset.mem_filter.mp hiC).2
        · have hiR : i ∈ R := by
            change i ∈ Finset.univ \ C
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiC⟩
          by_cases hiS : i ∈ S
          · exact Or.inr (Or.inl (ha i hiS))
          · exact Or.inr (Or.inr (hb i (Finset.mem_sdiff.mpr ⟨hiR, hiS⟩)))
      rcases hkill with hkill | hkill | hkill
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
    have hBexact : ∀ i : Fin 9,
        ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).card = 3 := by
      intro i
      let A := (Finset.univ.erase i).filter (fun l => ip (u l) (u i) = 0)
      let B := (Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)
      let C := (Finset.univ.erase i).filter (fun l => ip (z l) (z i) = 0)
      have hAi : A.card ≤ 2 := by
        apply le_trans (Finset.card_le_card ?_) (hAcard (u i) (hu i))
        intro l hl
        simp only [A, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hBi : B.card ≤ 3 := by
        apply le_trans (Finset.card_le_card ?_) (hBcard (w i) (hw i))
        intro l hl
        simp only [B, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hCi : C.card ≤ 3 := by
        apply le_trans (Finset.card_le_card ?_) (hCcard (z i) (hz i))
        intro l hl
        simp only [C, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hcover : Finset.univ.erase i ⊆ A ∪ B ∪ C := by
        intro l hl
        have hli : l ≠ i := (Finset.mem_erase.mp hl).1
        rcases mul_eq_zero.mp (horth i l (Ne.symm hli)) with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hl,
                (ip_eq_zero_comm (x := u i) (y := u l)).mp h⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hl,
                (ip_eq_zero_comm (x := w i) (y := w l)).mp h⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hl,
              (ip_eq_zero_comm (x := z i) (y := z l)).mp h⟩)
      have hlow : 8 ≤ A.card + B.card + C.card := by
        have hle : 8 ≤ (A ∪ B ∪ C).card := by
          have := Finset.card_le_card hcover
          simpa using this
        have hab := Finset.card_union_le A B
        have habc := Finset.card_union_le (A ∪ B) C
        omega
      have hAfull : (Finset.univ.filter (fun l => ip (u l) (u i) = 0)).card ≤ 2 :=
        hAcard (u i) (hu i)
      have hCfull : (Finset.univ.filter (fun l => ip (z l) (z i) = 0)).card ≤ 3 :=
        hCcard (z i) (hz i)
      have hAembed : A.card ≤
          (Finset.univ.filter (fun l => ip (u l) (u i) = 0)).card := by
        apply Finset.card_le_card
        intro l hl
        simp only [A, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hCembed : C.card ≤
          (Finset.univ.filter (fun l => ip (z l) (z i) = 0)).card := by
        apply Finset.card_le_card
        intro l hl
        simp only [C, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      change B.card = 3
      omega
    let F : Fin 9 → Finset (Fin 9 × Fin 9) := fun i =>
      ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
        (fun l => (i, l))
    let E : Finset (Fin 9 × Fin 9) := Finset.univ.biUnion F
    have hFcard : ∀ i : Fin 9, (F i).card = 3 := by
      intro i
      change (((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
        (fun l => (i, l))).card = 3
      rw [Finset.card_image_iff.mpr]
      · exact hBexact i
      · intro a ha b hb hab
        exact congrArg Prod.snd hab
    have hEcard : E.card = 27 := by
      change (Finset.univ.biUnion F).card = 27
      rw [Finset.card_biUnion]
      · simp [hFcard]
      · intro i hi j hj hij
        apply Finset.disjoint_left.2
        intro p hpi hpj
        change p ∈
          ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
            (fun l => (i, l)) at hpi
        change p ∈
          ((Finset.univ.erase j).filter (fun l => ip (w l) (w j) = 0)).image
            (fun l => (j, l)) at hpj
        rcases Finset.mem_image.mp hpi with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hpj with ⟨b, hb, hab⟩
        simp only [Prod.mk.injEq] at hab
        exact hij hab.1.symm
    have hEclosed : ∀ p ∈ E, (p.2, p.1) ∈ E := by
      intro p hp
      change p ∈ Finset.univ.biUnion F at hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      change p ∈
        ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
          (fun l => (i, l)) at hpi
      rcases Finset.mem_image.mp hpi with ⟨j, hj, rfl⟩
      have hji : j ≠ i := by
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
      have hzero : ip (w j) (w i) = 0 := (Finset.mem_filter.mp hj).2
      have hzero' : ip (w i) (w j) = 0 :=
        (ip_eq_zero_comm (x := w j) (y := w i)).mp hzero
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ j, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩, hzero'⟩, rfl⟩
    have hEven : Even E.card := by
      apply even_card_of_involutive (fun p : Fin 9 × Fin 9 => (p.2, p.1))
      · intro p
        cases p
        rfl
      · exact hEclosed
      · intro p hp hsame
        have hbi := Finset.mem_biUnion.mp hp
        obtain ⟨i, hi, hpi⟩ := hbi
        change p ∈
          ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
            (fun l => (i, l)) at hpi
        rcases Finset.mem_image.mp hpi with ⟨j, hj, rfl⟩
        have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
        have hpair : j = i ∧ i = j := by
          simpa [Prod.ext_iff] using hsame
        have hji : j = i := hpair.1
        exact hne hji
    rw [hEcard] at hEven
    norm_num at hEven


end Lower

abbrev IsUPB (m : ℕ) : Prop :=
  ∃ u : Fin m → Fin 3 → ℂ,
  ∃ w : Fin m → Fin 4 → ℂ,
  ∃ z : Fin m → Fin 4 → ℂ,
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
        (∑ r, star (z i r) * c r) ≠ 0)

theorem proof : IsLeast {m : ℕ | IsUPB m} 10 := by
  refine ⟨Upper.upperProof, ?_⟩
  intro m hm
  by_contra hlt
  exact Lower.lowerProof m (by omega) hm

end Submissions.MinUPB344Exact.Composed
