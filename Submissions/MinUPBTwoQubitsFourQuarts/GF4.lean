import Mathlib

namespace Submissions.MinUPBTwoQubitsFourQuarts.GF4

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

abbrev dims : Fin 6 → ℕ := fun j => if j.val < 2 then 2 else 4

def qFrame : Fin 16 → Fin 4 → ℤ := ![
  ![-2, -3, 1, -2], ![3, -2, 2, 1], ![-1, -2, -2, 3], ![2, -1, -3, -2],
  ![-3, 1, -3, -2], ![-1, -3, 2, -3], ![3, -2, -3, -1], ![2, 3, 1, -3],
  ![1, 3, -3, -2], ![-3, 1, 2, -3], ![3, -2, 1, -3], ![2, 3, 3, 1],
  ![3, 3, 2, -1], ![-3, 3, 1, 2], ![-2, -1, 3, -3], ![1, -2, 3, 3]]

def perm0 : Fin 16 → Fin 16 := ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
def perm1 : Fin 16 → Fin 16 := ![0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3]
def perm2 : Fin 16 → Fin 16 := ![0, 4, 8, 12, 9, 13, 1, 5, 14, 10, 6, 2, 7, 3, 15, 11]
def perm3 : Fin 16 → Fin 16 := ![0, 4, 8, 12, 13, 9, 5, 1, 6, 2, 14, 10, 11, 15, 3, 7]

def perm : Fin 4 → Fin 16 → Fin 16
  | ⟨0, _⟩ => perm0
  | ⟨1, _⟩ => perm1
  | ⟨2, _⟩ => perm2
  | ⟨3, _⟩ => perm3

def quartZ (k : Fin 4) (i : Fin 16) : Fin 4 → ℤ :=
  qFrame (perm k i)

def degZ : Fin 16 → Fin 2 → ℤ := ![
  ![1, 1], ![-1, 1], ![1, 1], ![-1, 1],
  ![1, 2], ![-2, 1], ![1, 2], ![-2, 1],
  ![1, 3], ![-3, 1], ![1, 3], ![-3, 1],
  ![1, 4], ![-4, 1], ![1, 4], ![-4, 1]]

def ordZ : Fin 16 → Fin 2 → ℤ := ![
  ![1, 1], ![1, 5], ![-1, 1], ![-5, 1],
  ![1, 2], ![1, 6], ![-2, 1], ![-6, 1],
  ![1, 3], ![1, 7], ![-3, 1], ![-7, 1],
  ![1, 4], ![1, 8], ![-4, 1], ![-8, 1]]

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

theorem nzDeg : ∀ i : Fin 16, ∃ r, degZ i r ≠ 0 := by decide

theorem nzOrd : ∀ i : Fin 16, ∃ r, ordZ i r ≠ 0 := by decide

theorem nzQuart : ∀ k : Fin 4, ∀ i : Fin 16, ∃ r, quartZ k i r ≠ 0 := by decide

theorem orthZ :
    ∀ i i' : Fin 16, i ≠ i' →
      dot2Z (degZ i) (degZ i') = 0 ∨
      dot2Z (ordZ i) (ordZ i') = 0 ∨
      ∃ k : Fin 4, dot4Z (quartZ k i) (quartZ k i') = 0 := by decide

theorem genQuart :
    ∀ k : Fin 4, ∀ i j l n : Fin 16, i < j → j < l → l < n →
      det4Z (quartZ k i) (quartZ k j) (quartZ k l) (quartZ k n) ≠ 0 := by decide

theorem nonparallelOrd :
    ∀ i j : Fin 16, i ≠ j → det2Z (ordZ i) (ordZ j) ≠ 0 := by decide

theorem genDeg :
    ∀ i j k : Fin 16, i < j → j < k →
      det2Z (degZ i) (degZ j) ≠ 0 ∨
      det2Z (degZ i) (degZ k) ≠ 0 ∨
      det2Z (degZ j) (degZ k) ≠ 0 := by decide

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

lemma killDeg :
    ∀ a : Fin 2 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 16),
        (∀ i ∈ S, ∑ r, star ((degZ i r : ℂ)) * a r = 0) → S.card ≤ 2 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 3 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 3 ≃o T := T.orderIsoOfFin hTcard
  have hgen := genDeg (e 0).1 (e 1).1 (e 2).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
  have hkill (i : Fin 3) :
      ∑ r, star ((degZ (e i).1 r : ℂ)) * a r = 0 :=
    hS (e i).1 (hT (e i).property)
  rcases hgen with h | h | h
  · exact ha (kill2 h (hkill 0) (hkill 1))
  · exact ha (kill2 h (hkill 0) (hkill 2))
  · exact ha (kill2 h (hkill 1) (hkill 2))

lemma killOrd :
    ∀ a : Fin 2 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 16),
        (∀ i ∈ S, ∑ r, star ((ordZ i r : ℂ)) * a r = 0) → S.card ≤ 1 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 2 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 2 ≃o T := T.orderIsoOfFin hTcard
  have hne : (e 0).1 ≠ (e 1).1 := by
    exact ne_of_lt (e.strictMono (by decide))
  have hdet : det2Z (ordZ (e 0).1) (ordZ (e 1).1) ≠ 0 :=
    nonparallelOrd _ _ hne
  exact ha (kill2 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property)))

lemma killQuart (k : Fin 4) :
    ∀ a : Fin 4 → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin 16),
        (∀ i ∈ S, ∑ r, star ((quartZ k i r : ℂ)) * a r = 0) → S.card ≤ 3 := by
  intro a ha S hS
  by_contra hcard
  have hcard' : 4 ≤ S.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard'
  let e : Fin 4 ≃o T := T.orderIsoOfFin hTcard
  have hdet := genQuart k (e 0).1 (e 1).1 (e 2).1 (e 3).1
      (e.strictMono (by decide)) (e.strictMono (by decide))
      (e.strictMono (by decide))
  exact ha (kill4 hdet
    (hS (e 0).1 (hT (e 0).property))
    (hS (e 1).1 (hT (e 1).property))
    (hS (e 2).1 (hT (e 2).property))
    (hS (e 3).1 (hT (e 3).property)))

def v : Fin 16 → (j : Fin 6) → Fin (dims j) → ℂ :=
  fun i =>
    Fin.cases
      (fun r => (degZ i r : ℂ))
      (fun j =>
        Fin.cases
          (fun r => (ordZ i r : ℂ))
          (fun k r => (quartZ k i r : ℂ))
          j)

@[simp] theorem v_zero (i : Fin 16) :
    v i 0 = fun r => (degZ i r : ℂ) := rfl

@[simp] theorem v_one (i : Fin 16) :
    v i 1 = fun r => (ordZ i r : ℂ) := rfl

@[simp] theorem v_quart (i : Fin 16) (k : Fin 4) :
    v i (Fin.succ (Fin.succ k)) = fun r => (quartZ k i r : ℂ) := rfl

def killing : Fin 6 → ℕ := fun j => if j.val = 0 then 2 else if j.val = 1 then 1 else 3

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
      ∃ w : Fin m → (j : Fin 6) → Fin (dims j) → ℂ,
        (∀ i j, w i j ≠ 0) ∧
        (∀ i i', i ≠ i' → ∃ j, (∑ r, star (w i j r) * w i' j r) = 0) ∧
        (∀ a : (j : Fin 6) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (w i j r) * a j r) ≠ 0) := by
  refine ⟨16, by decide, ?_⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · obtain ⟨r, hr⟩ := nzDeg i
      intro h
      exact hr (by
        have hz := congrFun h r
        simpa using hz)
    · refine Fin.cases ?_ (fun k => ?_) k
      · obtain ⟨r, hr⟩ := nzOrd i
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
    rcases orthZ i i' hne with hD | hO | ⟨k, hQ⟩
    · refine ⟨0, ?_⟩
      rw [v_zero, v_zero]
      calc
        (∑ r, star ((degZ i r : ℂ)) * (degZ i' r : ℂ)) =
            (dot2Z (degZ i) (degZ i') : ℂ) := dot2_cast _ _
        _ = 0 := by exact_mod_cast hD
    · refine ⟨1, ?_⟩
      rw [v_one, v_one]
      calc
        (∑ r, star ((ordZ i r : ℂ)) * (ordZ i' r : ℂ)) =
            (dot2Z (ordZ i) (ordZ i') : ℂ) := dot2_cast _ _
        _ = 0 := by exact_mod_cast hO
    · refine ⟨Fin.succ (Fin.succ k), ?_⟩
      rw [v_quart, v_quart]
      calc
        (∑ r, star ((quartZ k i r : ℂ)) * (quartZ k i' r : ℂ)) =
            (dot4Z (quartZ k i) (quartZ k i') : ℂ) := dot4_cast _ _
        _ = 0 := by exact_mod_cast hQ
  · intro a ha
    have hbudget : (∑ j, killing j) < 16 := by decide
    have hkill :
        ∀ j : Fin 6, ∀ b : Fin (dims j) → ℂ, b ≠ 0 →
          ∀ S : Finset (Fin 16),
            (∀ i ∈ S, (∑ r, star (v i j r) * b r) = 0) →
              S.card ≤ killing j := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro b hb S hS
        have hk := killDeg b hb S (by
          intro i hi
          have hh := hS i hi
          rw [v_zero] at hh
          exact hh)
        simpa [killing] using hk
      · refine Fin.cases ?_ (fun k => ?_) k
        · intro b hb S hS
          have hk := killOrd b hb S (by
            intro i hi
            have hh := hS i hi
            change (∑ r, star (v i 1 r) * b r) = 0 at hh
            rw [v_one] at hh
            exact hh)
          simpa [killing] using hk
        · intro b hb S hS
          have hk := killQuart k b hb S (by
            intro i hi
            have hh := hS i hi
            rw [v_quart] at hh
            exact hh)
          simpa [killing] using hk
    exact budget 6 16 dims killing v hbudget hkill a ha

end Submissions.MinUPBTwoQubitsFourQuarts.GF4
