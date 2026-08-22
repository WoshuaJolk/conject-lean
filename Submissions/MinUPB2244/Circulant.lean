import Mathlib

namespace Submissions.MinUPB2244.Circulant

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

abbrev dims : Fin 4 → ℕ := fun j => if j.val < 2 then 2 else 4

/-- Qubit factor 1: pairs of the perfect matching `{0,3},{6,9},{2,5},{8,1},{4,7}`
(one matching of the distance-3 10-cycle) get orthogonal pairs `(1,c), (-c,1)`. -/
def qubitAZ : Fin 10 → Fin 2 → ℤ := ![
  ![1, 1], ![-4, 1], ![1, 3], ![-1, 1], ![1, 5],
  ![-3, 1], ![1, 2], ![-5, 1], ![1, 4], ![-2, 1]]

/-- Qubit factor 2: the other matching `{3,6},{9,2},{5,8},{1,4},{7,0}` of the same 10-cycle. -/
def qubitBZ : Fin 10 → Fin 2 → ℤ := ![
  ![-5, 1], ![1, 4], ![-2, 1], ![1, 1], ![-4, 1],
  ![1, 3], ![-1, 1], ![1, 5], ![-3, 1], ![1, 2]]

/-- Ordinary quart factor: general-position vectors orthogonal on the pentagonal prism
`C_10(4,5)` (distance-4 and distance-5 edges of `Z_10`). Every four are independent. -/
def prismZ : Fin 10 → Fin 4 → ℤ := ![
  ![1, 1, -1, 0], ![4, -5, 4, -8], ![2, -1, 2, 0], ![2, -3, 0, -4], ![2, -1, 1, -1],
  ![-1, 0, -1, -1], ![2, -8, -6, 3], ![6, 8, -2, -3], ![1, -2, -2, 2], ![2, 0, -3, 1]]

/-- Degenerate quart factor: the `SpanningOrthRep4C10` vectors, orthogonality graph exactly
the circulant `C_10(1,2)`, no five in a common hyperplane (killing number 4). -/
def circZ : Fin 10 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![0, 2, -1, 0], ![0, 0, 0, 2], ![1, 1, 2, 0], ![2, -2, 0, 0],
  ![-2, -2, 2, 2], ![-2, -2, -2, -2], ![2, -2, 2, -2], ![0, -2, 0, 2], ![0, -1, -2, -1]]

def quartZ : Fin 2 → Fin 10 → Fin 4 → ℤ
  | ⟨0, _⟩ => prismZ
  | ⟨1, _⟩ => circZ

def dot2Z (x y : Fin 2 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def det2Z (x y : Fin 2 → ℤ) : ℤ :=
  x 0 * y 1 - x 1 * y 0

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

theorem nzA : ∀ i : Fin 10, ∃ r, qubitAZ i r ≠ 0 := by decide

theorem nzB : ∀ i : Fin 10, ∃ r, qubitBZ i r ≠ 0 := by decide

theorem nzQuart : ∀ k : Fin 2, ∀ i : Fin 10, ∃ r, quartZ k i r ≠ 0 := by decide

/-- Every pair of distinct states is orthogonal in some factor: the four orthogonality
classes partition `E(K_10)` (distance 3 split between the qubits, distances 4,5 on the
prism factor, distances 1,2 on the degenerate factor). -/
theorem orthZ :
    ∀ i i' : Fin 10, i ≠ i' →
      dot2Z (qubitAZ i) (qubitAZ i') = 0 ∨
      dot2Z (qubitBZ i) (qubitBZ i') = 0 ∨
      ∃ k : Fin 2, dot4Z (quartZ k i) (quartZ k i') = 0 := by decide

theorem nonparallelA :
    ∀ i j : Fin 10, i ≠ j → det2Z (qubitAZ i) (qubitAZ j) ≠ 0 := by decide

theorem nonparallelB :
    ∀ i j : Fin 10, i ≠ j → det2Z (qubitBZ i) (qubitBZ j) ≠ 0 := by decide

/-- The prism factor is in general position: every four vectors independent. -/
theorem genPrism :
    ∀ i j l n : Fin 10, i < j → j < l → l < n →
      det4Z (prismZ i) (prismZ j) (prismZ l) (prismZ n) ≠ 0 := by decide

/-- No five of the degenerate factor's vectors lie in a common hyperplane: every five
contain four independent ones. -/
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

lemma dot4_cast (x y : Fin 4 → ℤ) :
    (∑ r, star ((x r : ℂ)) * (y r : ℂ)) = (dot4Z x y : ℂ) := by
  simp [dot4Z, Fin.sum_univ_four, star_intCast]

lemma killA :
    ∀ a : Fin 2 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((qubitAZ i r : ℂ)) * a r = 0) → S.card ≤ 1 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 2 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 2 ≃o T := T.orderIsoOfFin hTcard
  have hne : (e 0).1 ≠ (e 1).1 := by
    exact ne_of_lt (e.strictMono (by decide))
  have hdet : det2Z (qubitAZ (e 0).1) (qubitAZ (e 1).1) ≠ 0 :=
    nonparallelA _ _ hne
  exact ha (kill2 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property)))

lemma killB :
    ∀ a : Fin 2 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((qubitBZ i r : ℂ)) * a r = 0) → S.card ≤ 1 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 2 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 2 ≃o T := T.orderIsoOfFin hTcard
  have hne : (e 0).1 ≠ (e 1).1 := by
    exact ne_of_lt (e.strictMono (by decide))
  have hdet : det2Z (qubitBZ (e 0).1) (qubitBZ (e 1).1) ≠ 0 :=
    nonparallelB _ _ hne
  exact ha (kill2 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property)))

lemma killPrism :
    ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((prismZ i r : ℂ)) * a r = 0) → S.card ≤ 3 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 4 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 4 ≃o T := T.orderIsoOfFin hTcard
  have hdet := genPrism (e 0).1 (e 1).1 (e 2).1 (e 3).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (e.strictMono (by decide))
  exact ha (kill4 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property))
    (hS (e 2).1 (hT (e 2).property))
    (hS (e 3).1 (hT (e 3).property)))

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

/-- Killing numbers: 1 for each qubit matching, 3 for the general-position prism factor,
4 for the degenerate `C_10(1,2)` factor. Their sum 9 is below `m = 10`. -/
def killing : Fin 4 → ℕ := fun j =>
  if j.val = 0 then 1 else if j.val = 1 then 1 else if j.val = 2 then 3 else 4

lemma killQuart (k : Fin 2) :
    ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 10),
        (∀ i ∈ S, ∑ r, star ((quartZ k i r : ℂ)) * a r = 0) →
          S.card ≤ killing (Fin.succ (Fin.succ k)) := by
  fin_cases k
  · intro a ha S hS
    have hk := killPrism a ha S (by
      intro i hi
      exact hS i hi)
    simpa [killing] using hk
  · intro a ha S hS
    have hk := killCirc a ha S (by
      intro i hi
      exact hS i hi)
    simpa [killing] using hk

def v : Fin 10 → (j : Fin 4) → Fin (dims j) → ℂ :=
  fun i =>
    Fin.cases
      (fun r => (qubitAZ i r : ℂ))
      (fun j =>
        Fin.cases
          (fun r => (qubitBZ i r : ℂ))
          (fun k r => (quartZ k i r : ℂ))
          j)

@[simp] theorem v_zero (i : Fin 10) :
    v i 0 = fun r => (qubitAZ i r : ℂ) := rfl

@[simp] theorem v_one (i : Fin 10) :
    v i 1 = fun r => (qubitBZ i r : ℂ) := rfl

@[simp] theorem v_quart (i : Fin 10) (k : Fin 2) :
    v i (Fin.succ (Fin.succ k)) = fun r => (quartZ k i r : ℂ) := rfl

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
    · obtain ⟨r, hr⟩ := nzA i
      intro h
      exact hr (by
        have hz := congrFun h r
        simpa using hz)
    · refine Fin.cases ?_ (fun k => ?_) k
      · obtain ⟨r, hr⟩ := nzB i
        intro h
        exact hr (by
          have hz := congrFun h r
          simpa using hz)
      · obtain ⟨r, hr⟩ := nzQuart k i
        intro h
        have hz := congrFun h r
        change (quartZ k i r : ℂ) = 0 at hz
        exact hr (by exact_mod_cast hz)
  · intro i i' hne
    rcases orthZ i i' hne with hA | hB | ⟨k, hQ⟩
    · refine ⟨0, ?_⟩
      rw [v_zero, v_zero]
      calc
        (∑ r, star ((qubitAZ i r : ℂ)) * (qubitAZ i' r : ℂ)) =
            (dot2Z (qubitAZ i) (qubitAZ i') : ℂ) := dot2_cast _ _
        _ = 0 := by exact_mod_cast hA
    · refine ⟨1, ?_⟩
      rw [v_one, v_one]
      calc
        (∑ r, star ((qubitBZ i r : ℂ)) * (qubitBZ i' r : ℂ)) =
            (dot2Z (qubitBZ i) (qubitBZ i') : ℂ) := dot2_cast _ _
        _ = 0 := by exact_mod_cast hB
    · refine ⟨Fin.succ (Fin.succ k), ?_⟩
      rw [v_quart, v_quart]
      calc
        (∑ r, star ((quartZ k i r : ℂ)) * (quartZ k i' r : ℂ)) =
            (dot4Z (quartZ k i) (quartZ k i') : ℂ) := dot4_cast _ _
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
        have hk := killA b hb S (by
          intro i hi
          have hh := hS i hi
          rw [v_zero] at hh
          exact hh)
        simpa [killing] using hk
      · refine Fin.cases ?_ (fun k => ?_) k
        · intro b hb S hS
          have hk := killB b hb S (by
            intro i hi
            have hh := hS i hi
            change (∑ r, star (v i 1 r) * b r) = 0 at hh
            rw [v_one] at hh
            exact hh)
          simpa [killing] using hk
        · intro b hb S hS
          exact killQuart k b hb S (by
            intro i hi
            have hh := hS i hi
            rw [v_quart] at hh
            exact hh)
    exact budget 4 10 dims killing v hbudget hkill a ha

end Submissions.MinUPB2244.Circulant
