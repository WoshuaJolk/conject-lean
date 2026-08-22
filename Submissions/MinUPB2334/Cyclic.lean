import Mathlib

namespace Submissions.MinUPB2334.Cyclic

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

abbrev dims : Fin 4 → ℕ := fun j => if j.val = 0 then 2 else if j.val < 3 then 3 else 4

/-- Qubit factor: the antipodal pairs `{i, i+5}` of `Z_10` get orthogonal pairs
`(1,c), (-c,1)`, `c = 1..5`. -/
def qubitCZ : Fin 10 → Fin 2 → ℤ := ![
  ![1, 1], ![1, 2], ![1, 3], ![1, 4], ![1, 5],
  ![-1, 1], ![-2, 1], ![-3, 1], ![-4, 1], ![-5, 1]]

/-- First qutrit factor: orthogonal along the distance-3 class of `Z_10` (the 10-cycle
`0-3-6-9-2-5-8-1-4-7-0`), every three vectors linearly independent. -/
def qutritD3Z : Fin 10 → Fin 3 → ℤ := ![
  ![2, -1, 1], ![-1, -1, -3], ![0, -2, 3], ![1, -1, -3], ![3, 0, -1],
  ![-1, 6, 4], ![1, -2, 1], ![-1, -5, -3], ![-2, -1, 1], ![-4, -3, -2]]

/-- Second qutrit factor: orthogonal along the distance-4 class of `Z_10` (two 5-cycles,
on the even and on the odd vertices), every three vectors linearly independent. -/
def qutritD4Z : Fin 10 → Fin 3 → ℤ := ![
  ![1, 1, 0], ![1, 1, 1], ![0, -6, -1], ![1, -4, -2], ![3, -3, 1],
  ![2, -3, 1], ![-1, 1, -6], ![2, 3, -5], ![-3, -1, 6], ![-2, -1, 1]]

/-- Degenerate quart factor: the `SpanningOrthRep4C10` vectors, orthogonality graph exactly
the circulant `C_10(1,2)`, no five in a common hyperplane (killing number 4). -/
def circZ : Fin 10 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![0, 2, -1, 0], ![0, 0, 0, 2], ![1, 1, 2, 0], ![2, -2, 0, 0],
  ![-2, -2, 2, 2], ![-2, -2, -2, -2], ![2, -2, 2, -2], ![0, -2, 0, 2], ![0, -1, -2, -1]]

def dot2Z (x y : Fin 2 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1

def dot3Z (x y : Fin 3 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def det2Z (x y : Fin 2 → ℤ) : ℤ :=
  x 0 * y 1 - x 1 * y 0

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

theorem nzC : ∀ i : Fin 10, ∃ r, qubitCZ i r ≠ 0 := by decide

theorem nzD3 : ∀ i : Fin 10, ∃ r, qutritD3Z i r ≠ 0 := by decide

theorem nzD4 : ∀ i : Fin 10, ∃ r, qutritD4Z i r ≠ 0 := by decide

theorem nzCirc : ∀ i : Fin 10, ∃ r, circZ i r ≠ 0 := by decide

/-- Every pair of distinct states is orthogonal in some factor: the four orthogonality
classes are the distance classes of `Z_10` — distance 5 on the qubit, distance 3 on the
first qutrit, distance 4 on the second, distances 1,2 on the degenerate quart. -/
theorem orthZ :
    ∀ i i' : Fin 10, i ≠ i' →
      dot2Z (qubitCZ i) (qubitCZ i') = 0 ∨
      dot3Z (qutritD3Z i) (qutritD3Z i') = 0 ∨
      dot3Z (qutritD4Z i) (qutritD4Z i') = 0 ∨
      dot4Z (circZ i) (circZ i') = 0 := by decide

theorem nonparallelC :
    ∀ i j : Fin 10, i ≠ j → det2Z (qubitCZ i) (qubitCZ j) ≠ 0 := by decide

/-- The first qutrit factor is in general position: every three vectors independent. -/
theorem genD3 :
    ∀ i j l : Fin 10, i < j → j < l →
      det3Z (qutritD3Z i) (qutritD3Z j) (qutritD3Z l) ≠ 0 := by decide

/-- The second qutrit factor is in general position: every three vectors independent. -/
theorem genD4 :
    ∀ i j l : Fin 10, i < j → j < l →
      det3Z (qutritD4Z i) (qutritD4Z j) (qutritD4Z l) ≠ 0 := by decide

/-- No five of the degenerate factor's vectors lie in a common hyperplane. -/
theorem span5Circ :
    ∀ i j k l t : Fin 10, i < j → j < k → k < l → l < t →
      det4Z (circZ i) (circZ j) (circZ k) (circZ l) ≠ 0 ∨
      det4Z (circZ i) (circZ j) (circZ k) (circZ t) ≠ 0 ∨
      det4Z (circZ i) (circZ j) (circZ l) (circZ t) ≠ 0 ∨
      det4Z (circZ i) (circZ k) (circZ l) (circZ t) ≠ 0 ∨
      det4Z (circZ j) (circZ k) (circZ l) (circZ t) ≠ 0 := by decide

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
    simp [M, Matrix.det_succ_row_zero, det3Z, Fin.sum_univ_succ,
      Fin.val_zero, Fin.zero_succAbove, Fin.val_succ, Fin.val_eq_zero,
      Fin.succ_succAbove_zero, Fin.succ_succAbove_one, Fin.succAbove]
    ring
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

lemma dot2_cast (x y : Fin 2 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot2Z x y : ℂ) := by
  simp [dot2Z, Fin.sum_univ_two, star_intCast]

lemma dot3_cast (x y : Fin 3 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot3Z x y : ℂ) := by
  simp [dot3Z, Fin.sum_univ_three, star_intCast]

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

lemma killC :
    ∀ a : Fin 2 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((qubitCZ i r : ℂ)) * a r = 0) → S.card ≤ 1 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 2 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 2 ≃o T := T.orderIsoOfFin hTcard
  have hne : (e 0).1 ≠ (e 1).1 := by
    exact ne_of_lt (e.strictMono (by decide))
  have hdet : det2Z (qubitCZ (e 0).1) (qubitCZ (e 1).1) ≠ 0 :=
    nonparallelC _ _ hne
  exact ha (kill2 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property)))

lemma killD3 :
    ∀ a : Fin 3 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((qutritD3Z i r : ℂ)) * a r = 0) → S.card ≤ 2 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 3 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 3 ≃o T := T.orderIsoOfFin hTcard
  have hdet := genD3 (e 0).1 (e 1).1 (e 2).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
  exact ha (kill3 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property))
    (hS (e 2).1 (hT (e 2).property)))

lemma killD4 :
    ∀ a : Fin 3 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((qutritD4Z i r : ℂ)) * a r = 0) → S.card ≤ 2 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 3 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 3 ≃o T := T.orderIsoOfFin hTcard
  have hdet := genD4 (e 0).1 (e 1).1 (e 2).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
  exact ha (kill3 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property))
    (hS (e 2).1 (hT (e 2).property)))

lemma killCirc :
    ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((circZ i r : ℂ)) * a r = 0) → S.card ≤ 4 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 5 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 5 ≃o T := T.orderIsoOfFin hTcard
  have hkill (i : Fin 5) :
      ∑ r, star ((circZ (e i).1 r : ℂ)) * a r = 0 :=
    hS (e i).1 (hT (e i).property)
  have hspan := span5Circ (e 0).1 (e 1).1 (e 2).1 (e 3).1 (e 4).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (e.strictMono (by decide)) (e.strictMono (by decide))
  rcases hspan with h | h | h | h | h
  · exact ha (kill4 h (hkill 0) (hkill 1) (hkill 2) (hkill 3))
  · exact ha (kill4 h (hkill 0) (hkill 1) (hkill 2) (hkill 4))
  · exact ha (kill4 h (hkill 0) (hkill 1) (hkill 3) (hkill 4))
  · exact ha (kill4 h (hkill 0) (hkill 2) (hkill 3) (hkill 4))
  · exact ha (kill4 h (hkill 1) (hkill 2) (hkill 3) (hkill 4))

def v : Fin 10 → (j : Fin 4) → Fin (dims j) → ℂ :=
  fun i =>
    Fin.cases
      (fun r => (qubitCZ i r : ℂ))
      (fun j =>
        Fin.cases
          (fun r => (qutritD3Z i r : ℂ))
          (fun k =>
            Fin.cases
              (fun r => (qutritD4Z i r : ℂ))
              (fun _ r => (circZ i r : ℂ))
              k)
          j)

@[simp] theorem v_zero (i : Fin 10) :
    v i 0 = fun r => (qubitCZ i r : ℂ) := rfl

@[simp] theorem v_one (i : Fin 10) :
    v i 1 = fun r => (qutritD3Z i r : ℂ) := rfl

@[simp] theorem v_two (i : Fin 10) :
    v i 2 = fun r => (qutritD4Z i r : ℂ) := rfl

@[simp] theorem v_circ (i : Fin 10) (k : Fin 1) :
    v i (Fin.succ (Fin.succ (Fin.succ k))) = fun r => (circZ i r : ℂ) := rfl

/-- Killing numbers: 1 for the qubit matching, 2 for each general-position qutrit factor,
4 for the degenerate `C_10(1,2)` factor. Their sum 9 is below `m = 10`. -/
def killing : Fin 4 → ℕ := fun j =>
  if j.val = 0 then 1 else if j.val = 1 then 2 else if j.val = 2 then 2 else 4

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
      ∃ w : Fin m → (j : Fin 4) → Fin (dims j) → ℂ,
        (∀ i j, w i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (w i j r) * w i' j r) = 0) ∧
        (∀ a : (j : Fin 4) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (w i j r) * a j r) ≠ 0) := by
  refine ⟨10, by decide, ?_⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · obtain ⟨r, hr⟩ := nzC i
      intro h
      exact hr (by
        have hz := congrFun h r
        simpa using hz)
    · refine Fin.cases ?_ (fun k => ?_) k
      · obtain ⟨r, hr⟩ := nzD3 i
        intro h
        exact hr (by
          have hz := congrFun h r
          simpa using hz)
      · refine Fin.cases ?_ (fun k => ?_) k
        · obtain ⟨r, hr⟩ := nzD4 i
          intro h
          exact hr (by
            have hz := congrFun h r
            simpa using hz)
        · obtain ⟨r, hr⟩ := nzCirc i
          intro h
          have hz := congrFun h r
          change (circZ i r : ℂ) = 0 at hz
          exact hr (by exact_mod_cast hz)
  · intro i i' hne
    rcases orthZ i i' hne with hC | hD3 | hD4 | hQ
    · refine ⟨0, ?_⟩
      rw [v_zero, v_zero]
      calc
        (∑ r, star ((qubitCZ i r : ℂ)) * (qubitCZ i' r : ℂ)) =
            (dot2Z (qubitCZ i) (qubitCZ i') : ℂ) := dot2_cast _ _
        _ = 0 := by exact_mod_cast hC
    · refine ⟨1, ?_⟩
      rw [v_one, v_one]
      calc
        (∑ r, star ((qutritD3Z i r : ℂ)) * (qutritD3Z i' r : ℂ)) =
            (dot3Z (qutritD3Z i) (qutritD3Z i') : ℂ) := dot3_cast _ _
        _ = 0 := by exact_mod_cast hD3
    · refine ⟨2, ?_⟩
      rw [v_two, v_two]
      calc
        (∑ r, star ((qutritD4Z i r : ℂ)) * (qutritD4Z i' r : ℂ)) =
            (dot3Z (qutritD4Z i) (qutritD4Z i') : ℂ) := dot3_cast _ _
        _ = 0 := by exact_mod_cast hD4
    · refine ⟨3, ?_⟩
      have h3 : (3 : Fin 4) = Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))) := rfl
      rw [h3, v_circ, v_circ]
      calc
        (∑ r, star ((circZ i r : ℂ)) * (circZ i' r : ℂ)) =
            (dot4Z (circZ i) (circZ i') : ℂ) := dot4_cast _ _
        _ = 0 := by exact_mod_cast hQ
  · intro a ha
    have hbudget : (∑ j, killing j) < 10 := by decide
    have hkill :
        ∀ j : Fin 4, ∀ b : Fin (dims j) → ℂ, b ≠ 0 →
          ∀ S : Finset (Fin 10),
            (∀ i ∈ S, (∑ r, star (v i j r) * b r) = 0) →
              S.card ≤ killing j := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro b hb S hS
        have hk := killC b hb S (by
          intro i hi
          have hh := hS i hi
          rw [v_zero] at hh
          exact hh)
        simpa [killing] using hk
      · refine Fin.cases ?_ (fun k => ?_) k
        · intro b hb S hS
          have hk := killD3 b hb S (by
            intro i hi
            have hh := hS i hi
            change (∑ r, star (v i 1 r) * b r) = 0 at hh
            rw [v_one] at hh
            exact hh)
          simpa [killing] using hk
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro b hb S hS
            have hk := killD4 b hb S (by
              intro i hi
              have hh := hS i hi
              change (∑ r, star (v i 2 r) * b r) = 0 at hh
              rw [v_two] at hh
              exact hh)
            simpa [killing] using hk
          · intro b hb S hS
            have hk := killCirc b hb S (by
              intro i hi
              have hh := hS i hi
              rw [v_circ] at hh
              exact hh)
            simpa [killing] using hk
    exact budget 4 10 dims killing v hbudget hkill a ha

end Submissions.MinUPB2334.Cyclic
