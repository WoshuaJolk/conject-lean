import Mathlib

namespace Submissions.TightSpanningOrthRep4C10.TightCirc10

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def vZ : Fin 10 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![1, 0, 0, 0]
  | ⟨1, _⟩ => ![0, 2, -1, 0]
  | ⟨2, _⟩ => ![0, 0, 0, 2]
  | ⟨3, _⟩ => ![1, 1, 2, 0]
  | ⟨4, _⟩ => ![2, -2, 0, 0]
  | ⟨5, _⟩ => ![-2, -2, 2, 2]
  | ⟨6, _⟩ => ![-2, -2, -2, -2]
  | ⟨7, _⟩ => ![2, -2, 2, -2]
  | ⟨8, _⟩ => ![0, -2, 0, 2]
  | ⟨9, _⟩ => ![0, -1, -2, -1]

def v (i : Fin 10) : Fin 4 → ℂ := fun r => (vZ i r : ℂ)

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

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

def minor3 (x y z : Fin 4 → ℤ) (c0 c1 c2 : Fin 4) : ℤ :=
  x c0 * y c1 * z c2 - x c0 * y c2 * z c1
    - x c1 * y c0 * z c2 + x c1 * y c2 * z c0
    + x c2 * y c0 * z c1 - x c2 * y c1 * z c0

theorem nzV : ∀ i : Fin 10, ∃ r, vZ i r ≠ 0 := by decide

theorem orthExact :
    ∀ i j : Fin 10, i ≠ j →
      ((let d := (i.val + 10 - j.val) % 10; min d (10 - d) = 1 ∨
        let d := (i.val + 10 - j.val) % 10; min d (10 - d) = 2) ↔
        dot4Z (vZ i) (vZ j) = 0) := by decide

theorem span5 :
    ∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t →
      det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
      det4Z (vZ i) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
      det4Z (vZ i) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ i) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
      det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by decide

theorem tight3 :
    ∀ i j k : Fin 10, i < j → j < k →
      minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0 := by decide

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

lemma linInd_of_det4 {x y z t : Fin 4 → ℤ} (hd : det4Z x y z t ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ)),
      (fun r : Fin 4 => (t r : ℂ))] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ);
       (t 0 : ℂ), (t 1 : ℂ), (t 2 : ℂ), (t 3 : ℂ)]
  have hdet : M.det = (det4Z x y z t : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det4Z, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 4 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam :
      (fun i : Fin 4 => M i) =
        ![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ), fun r => (t r : ℂ)] := by
    ext i r; fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd_v4 (i j k l : Fin 10) (hd : det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k, v l] := by
  have h := linInd_of_det4 hd
  convert h using 1
  ext s r; fin_cases s <;> simp [v]

lemma linInd3_of_minor012 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 1 2 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 0 1 2 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (0 : Fin 4), LinearMap.proj (R := ℂ) (1 : Fin 4),
      LinearMap.proj (R := ℂ) (2 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_of_minor013 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 1 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 3 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 0 1 3 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (0 : Fin 4), LinearMap.proj (R := ℂ) (1 : Fin 4),
      LinearMap.proj (R := ℂ) (3 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_of_minor023 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 2 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 2 : ℂ), (z 3 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 0 2 3 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (0 : Fin 4), LinearMap.proj (R := ℂ) (2 : Fin 4),
      LinearMap.proj (R := ℂ) (3 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_of_minor123 {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have : M.det = (minor3 x y z 1 2 3 : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [this]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) (1 : Fin 4), LinearMap.proj (R := ℂ) (2 : Fin 4),
      LinearMap.proj (R := ℂ) (3 : Fin 4)]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) =
        fun i => M i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, M]
  have : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ this

lemma linInd3_cols {x y z : Fin 4 → ℤ}
    (hd : minor3 x y z 0 1 2 ≠ 0 ∨ minor3 x y z 0 1 3 ≠ 0 ∨
          minor3 x y z 0 2 3 ≠ 0 ∨ minor3 x y z 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r : ℂ)),
      (fun r : Fin 4 => (y r : ℂ)),
      (fun r : Fin 4 => (z r : ℂ))] := by
  rcases hd with h | h | h | h
  · exact linInd3_of_minor012 h
  · exact linInd3_of_minor013 h
  · exact linInd3_of_minor023 h
  · exact linInd3_of_minor123 h

lemma linInd_v3 (i j k : Fin 10)
    (hd : minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
          minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
          minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
          minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  have h := linInd3_cols hd
  convert h using 1
  ext s r; fin_cases s <;> simp [v]

theorem proof :
    ∃ v : Fin 10 → Fin 4 → ℂ,
      (∀ i, v i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (((let d := (i.val + 10 - j.val) % 10; min d (10 - d)) = 1 ∨
          (let d := (i.val + 10 - j.val) % 10; min d (10 - d)) = 2) ↔
          (∑ r, star (v i r) * v j r) = 0)) ∧
      (∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t →
        LinearIndependent ℂ ![v i, v j, v k, v l] ∨
        LinearIndependent ℂ ![v i, v j, v k, v t] ∨
        LinearIndependent ℂ ![v i, v j, v l, v t] ∨
        LinearIndependent ℂ ![v i, v k, v l, v t] ∨
        LinearIndependent ℂ ![v j, v k, v l, v t]) ∧
      (∀ i j k : Fin 10, i < j → j < k → LinearIndependent ℂ ![v i, v j, v k]) := by
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr⟩ := nzV i
    apply hr
    have h := congr_fun hi r
    simpa [v] using h
  · intro i j hij
    constructor
    · intro he
      have hz : dot4Z (vZ i) (vZ j) = 0 := (orthExact i j hij).mp (by simpa using he)
      have hdot : (∑ r, star (v i r) * v j r) = (dot4Z (vZ i) (vZ j) : ℂ) := by
        simpa [v] using dot4_cast (vZ i) (vZ j)
      rw [hdot]; exact_mod_cast hz
    · intro hip
      have hdot : (∑ r, star (v i r) * v j r) = (dot4Z (vZ i) (vZ j) : ℂ) := by
        simpa [v] using dot4_cast (vZ i) (vZ j)
      have hz : dot4Z (vZ i) (vZ j) = 0 := by
        have := hdot.symm.trans hip; exact_mod_cast this
      exact (orthExact i j hij).mpr hz
  · intro i j k l t hij hjk hkl hlt
    rcases span5 i j k l t hij hjk hkl hlt with h | h | h | h | h
    · exact Or.inl (linInd_v4 i j k l h)
    · exact Or.inr <| Or.inl (linInd_v4 i j k t h)
    · exact Or.inr <| Or.inr <| Or.inl (linInd_v4 i j l t h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (linInd_v4 i k l t h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (linInd_v4 j k l t h)
  · intro i j k hij hjk
    exact linInd_v3 i j k (tight3 i j k hij hjk)

end Submissions.TightSpanningOrthRep4C10.TightCirc10
