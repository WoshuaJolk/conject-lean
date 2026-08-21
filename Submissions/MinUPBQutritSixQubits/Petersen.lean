import Mathlib

namespace Submissions.MinUPBQutritSixQubits.Petersen

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

abbrev dims : Fin 7 → ℕ := fun j => if j = 0 then 3 else 2

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

def qZ : Fin 6 → Fin 10 → Fin 2 → ℤ
  | ⟨0, _⟩ => ![![1, 1], ![1, 2], ![-1, 1], ![-2, 1],
    ![1, 3], ![-3, 1], ![1, 4], ![-4, 1], ![1, 5], ![-5, 1]]
  | ⟨1, _⟩ => ![![1, 1], ![1, 2], ![1, 3], ![-1, 1],
    ![-2, 1], ![1, 4], ![-3, 1], ![1, 5], ![-5, 1], ![-4, 1]]
  | ⟨2, _⟩ => ![![1, 1], ![1, 2], ![1, 3], ![1, 4],
    ![1, 5], ![-2, 1], ![-1, 1], ![-5, 1], ![-3, 1], ![-4, 1]]
  | ⟨3, _⟩ => ![![1, 1], ![1, 2], ![1, 3], ![1, 4],
    ![1, 5], ![-4, 1], ![-5, 1], ![-1, 1], ![-2, 1], ![-3, 1]]
  | ⟨4, _⟩ => ![![1, 1], ![1, 2], ![1, 3], ![1, 4],
    ![-3, 1], ![1, 5], ![-5, 1], ![-4, 1], ![-1, 1], ![-2, 1]]
  | ⟨5, _⟩ => ![![1, 1], ![1, 2], ![1, 3], ![1, 4],
    ![1, 5], ![-3, 1], ![-4, 1], ![-2, 1], ![-5, 1], ![-1, 1]]

def dot3Z (x y : Fin 3 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def dot2Z (x y : Fin 2 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1

def det3Z (x y z : Fin 3 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

def det2Z (x y : Fin 2 → ℤ) : ℤ := x 0 * y 1 - x 1 * y 0

theorem nzU : ∀ i : Fin 10, ∃ r, uZ i r ≠ 0 := by decide

theorem nzQ : ∀ k : Fin 6, ∀ i : Fin 10, ∃ r, qZ k i r ≠ 0 := by decide

theorem orthZ :
    ∀ i j : Fin 10, i ≠ j →
      dot3Z (uZ i) (uZ j) = 0 ∨
      ∃ k : Fin 6, dot2Z (qZ k i) (qZ k j) = 0 := by decide

theorem genU :
    ∀ i j k l : Fin 10, i < j → j < k → k < l →
      det3Z (uZ i) (uZ j) (uZ k) ≠ 0 ∨
      det3Z (uZ i) (uZ j) (uZ l) ≠ 0 ∨
      det3Z (uZ i) (uZ k) (uZ l) ≠ 0 ∨
      det3Z (uZ j) (uZ k) (uZ l) ≠ 0 := by decide

theorem nonparallelQ :
    ∀ k : Fin 6, ∀ i j : Fin 10, i ≠ j → det2Z (qZ k i) (qZ k j) ≠ 0 := by decide

lemma dot3_cast (x y : Fin 3 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot3Z x y : ℂ) := by
  simp [dot3Z, Fin.sum_univ_three, star_intCast]

lemma dot2_cast (x y : Fin 2 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = ((x 0 * y 0 + x 1 * y 1 : ℤ) : ℂ) := by
  simp [Fin.sum_univ_two, star_intCast]

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

lemma kill2 {x y : Fin 2 → ℤ} {a : Fin 2 → ℂ}
    (hd : det2Z x y ≠ 0)
    (hx : ∑ r, star ((x r : ℂ)) * a r = 0)
    (hy : ∑ r, star ((y r : ℂ)) * a r = 0) : a = 0 := by
  have h0 : (x 0 : ℂ) * a 0 + (x 1 : ℂ) * a 1 = 0 := by
    simpa [Fin.sum_univ_two, star_intCast] using hx
  have h1 : (y 0 : ℂ) * a 0 + (y 1 : ℂ) * a 1 = 0 := by
    simpa [Fin.sum_univ_two, star_intCast] using hy
  have hd' : (x 0 : ℂ) * (y 1 : ℂ) - (x 1 : ℂ) * (y 0 : ℂ) ≠ 0 := by
    exact_mod_cast hd
  funext r
  fin_cases r
  · apply (mul_eq_zero.mp ?_).resolve_left hd'
    calc
      ((x 0 : ℂ) * (y 1 : ℂ) - (x 1 : ℂ) * (y 0 : ℂ)) * a 0 =
          (y 1 : ℂ) * ((x 0 : ℂ) * a 0 + (x 1 : ℂ) * a 1) -
            (x 1 : ℂ) * ((y 0 : ℂ) * a 0 + (y 1 : ℂ) * a 1) := by ring
      _ = 0 := by rw [h0, h1]; ring
  · apply (mul_eq_zero.mp ?_).resolve_left hd'
    calc
      ((x 0 : ℂ) * (y 1 : ℂ) - (x 1 : ℂ) * (y 0 : ℂ)) * a 1 =
          (x 0 : ℂ) * ((y 0 : ℂ) * a 0 + (y 1 : ℂ) * a 1) -
            (y 0 : ℂ) * ((x 0 : ℂ) * a 0 + (x 1 : ℂ) * a 1) := by ring
      _ = 0 := by rw [h0, h1]; ring

lemma killU :
    ∀ a : Fin 3 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((uZ i r : ℂ)) * a r = 0) → S.card ≤ 3 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 4 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 4 ≃o T := T.orderIsoOfFin hTcard
  have hgen := genU (e 0).1 (e 1).1 (e 2).1 (e 3).1
      (e.strictMono (by decide)) (e.strictMono (by decide)) (e.strictMono (by decide))
  have hkill (i : Fin 4) :
      ∑ r, star ((uZ (e i).1 r : ℂ)) * a r = 0 :=
    hS (e i).1 (hT (e i).property)
  rcases hgen with h | h | h | h
  · exact ha (kill3 h (hkill 0) (hkill 1) (hkill 2))
  · exact ha (kill3 h (hkill 0) (hkill 1) (hkill 3))
  · exact ha (kill3 h (hkill 0) (hkill 2) (hkill 3))
  · exact ha (kill3 h (hkill 1) (hkill 2) (hkill 3))

lemma killQ (k : Fin 6) :
    ∀ a : Fin 2 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((qZ k i r : ℂ)) * a r = 0) → S.card ≤ 1 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 2 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 2 ≃o T := T.orderIsoOfFin hTcard
  have hne : (e 0).1 ≠ (e 1).1 := by
    exact ne_of_lt (e.strictMono (by decide))
  have hdet : det2Z (qZ k (e 0).1) (qZ k (e 1).1) ≠ 0 :=
    nonparallelQ k _ _ hne
  have h0 := hS (e 0).1 (hT (e 0).property)
  have h1 := hS (e 1).1 (hT (e 1).property)
  exact ha (kill2 hdet h0 h1)

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

def v : Fin 10 → (j : Fin 7) → Fin (dims j) → ℂ :=
  fun i =>
    Fin.cases
      (fun r => (uZ i r : ℂ))
      (fun k r => (qZ k i r : ℂ))

@[simp] theorem v_zero (i : Fin 10) :
    v i 0 = fun r => (uZ i r : ℂ) := rfl

@[simp] theorem v_succ (i : Fin 10) (k : Fin 6) :
    v i k.succ = fun r => (qZ k i r : ℂ) := rfl

def killing : Fin 7 → ℕ := fun j => if j = 0 then 3 else 1

theorem proof :
    ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
      ∃ w : Fin m → (j : Fin 7) → Fin (dims j) → ℂ,
        (∀ i j, w i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (w i j r) * w i' j r) = 0) ∧
        (∀ a : (j : Fin 7) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (w i j r) * a j r) ≠ 0) := by
  refine ⟨10, by decide, ?_⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · obtain ⟨r, hr⟩ := nzU i
      intro h
      have h' : (fun r => (uZ i r : ℂ)) = 0 := by
        simpa only [v_zero, dims] using h
      have hz := congrFun h' r
      have hz' : (uZ i r : ℂ) = 0 := by simpa using hz
      exact hr (by exact_mod_cast hz')
    · obtain ⟨r, hr⟩ := nzQ k i
      intro h
      have hkdim : dims k.succ = 2 := by simp [dims]
      have hz := congrFun h (Fin.cast hkdim.symm r)
      change (qZ k i (Fin.cast hkdim.symm r) : ℂ) = 0 at hz
      have hz' : (qZ k i r : ℂ) = 0 := by
        convert hz using 1
        congr 1
      exact hr (by exact_mod_cast hz')
  · intro i i' hne
    obtain h | ⟨k, hk⟩ := orthZ i i' hne
    · refine ⟨0, ?_⟩
      rw [v_zero, v_zero]
      calc
        (∑ r, star ((uZ i r : ℂ)) * (uZ i' r : ℂ)) =
            (dot3Z (uZ i) (uZ i') : ℂ) := dot3_cast _ _
        _ = 0 := by rw [h]; norm_num
    · refine ⟨k.succ, ?_⟩
      rw [v_succ, v_succ]
      calc
        (∑ r, star ((qZ k i r : ℂ)) * (qZ k i' r : ℂ)) =
            (dot2Z (qZ k i) (qZ k i') : ℂ) := by
              rw [dot2Z]
              exact dot2_cast (qZ k i) (qZ k i')
        _ = 0 := by exact_mod_cast hk
  · intro a ha
    have hbudget : (∑ j, killing j) < 10 := by decide
    have hkill :
        ∀ j : Fin 7, ∀ b : Fin (dims j) → ℂ, b ≠ 0 →
          ∀ S : Finset (Fin 10),
            (∀ i ∈ S, (∑ r, star (v i j r) * b r) = 0) →
              S.card ≤ killing j := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro b hb S hS
        apply killU b hb S
        intro i hi
        simpa [v_zero, dims] using hS i hi
      · intro b hb S hS
        simpa [killing, Fin.succ_ne_zero] using killQ k b hb S (by
          intro i hi
          have hh := hS i hi
          rw [v_succ] at hh
          exact hh)
    exact budget 7 10 dims killing v hbudget hkill a ha

end Submissions.MinUPBQutritSixQubits.Petersen
