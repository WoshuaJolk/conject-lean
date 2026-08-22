import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Submissions.RoundRobinRegularDecomposition.RoundRobin

section Blocks

variable {p : ℕ} (e : Fin p → ℕ)

/-- `e` extended to `ℕ` by zero. -/
def eExt (n : ℕ) : ℕ := if h : n < p then e ⟨n, h⟩ else 0

/-- Partial sums of the degree sequence: `T e n = e 0 + ⋯ + e (n-1)`. -/
def T (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, eExt e i

lemma T_mono : Monotone (T e) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_range] at *
  omega

lemma T_succ (n : ℕ) : T e (n + 1) = T e n + eExt e n := Finset.sum_range_succ _ _

lemma T_top : T e p = ∑ j, e j := by
  unfold T
  rw [← Fin.sum_univ_eq_sum_range (fun i => eExt e i) p]
  exact Finset.sum_congr rfl fun i _ => by simp [eExt, i.isLt]

/-- The (ℕ-valued) block index of `x`: the largest `j ≤ p` with `T e j ≤ x`. -/
def blockOfAux (x : ℕ) : ℕ := Nat.findGreatest (fun j => T e j ≤ x) p

lemma T_zero : T e 0 = 0 := by simp [T]

lemma T_blockOfAux_le (x : ℕ) : T e (blockOfAux e x) ≤ x :=
  Nat.findGreatest_spec (P := fun j => T e j ≤ x) (Nat.zero_le p)
    (by rw [T_zero]; exact Nat.zero_le x)

lemma blockOfAux_lt {x : ℕ} (hx : x < ∑ j, e j) : blockOfAux e x < p := by
  rcases lt_or_eq_of_le (Nat.findGreatest_le (P := fun j => T e j ≤ x) p) with h | h
  · exact h
  · exfalso
    have h1 : T e (blockOfAux e x) ≤ x := T_blockOfAux_le e x
    rw [show blockOfAux e x = p from h, T_top] at h1
    omega

lemma lt_T_blockOfAux_succ {x : ℕ} (hx : x < ∑ j, e j) :
    x < T e (blockOfAux e x + 1) := by
  by_contra hcon
  have h' : T e (blockOfAux e x + 1) ≤ x := Nat.le_of_not_lt hcon
  have hle : blockOfAux e x + 1 ≤ p := blockOfAux_lt e hx
  exact Nat.findGreatest_is_greatest (P := fun j => T e j ≤ x) (n := p)
    (k := blockOfAux e x + 1) (Nat.lt_succ_self _) hle h'

lemma blockOfAux_eq_iff {x : ℕ} (hx : x < ∑ j, e j) {j : ℕ} (hj : j < p) :
    blockOfAux e x = j ↔ T e j ≤ x ∧ x < T e (j + 1) := by
  constructor
  · rintro rfl
    exact ⟨T_blockOfAux_le e x, lt_T_blockOfAux_succ e hx⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (blockOfAux e x) j with h | h | h
    · exfalso
      have hm : T e (blockOfAux e x + 1) ≤ T e j := T_mono e (Nat.succ_le_of_lt h)
      have := lt_T_blockOfAux_succ e hx
      omega
    · exact h
    · exfalso
      have hm : T e (j + 1) ≤ T e (blockOfAux e x) := T_mono e (Nat.succ_le_of_lt h)
      have := T_blockOfAux_le e x
      omega

/-- The block index as an element of `Fin p`. -/
def blockOf (hp : 0 < p) (x : ℕ) : Fin p :=
  if h : blockOfAux e x < p then ⟨blockOfAux e x, h⟩ else ⟨0, hp⟩

lemma blockOf_eq_iff (hp : 0 < p) {x : ℕ} (hx : x < ∑ j, e j) (j : Fin p) :
    blockOf e hp x = j ↔ T e j.val ≤ x ∧ x < T e (j.val + 1) := by
  rw [blockOf, dif_pos (blockOfAux_lt e hx),
    ← blockOfAux_eq_iff e hx j.isLt]
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.ext h

/-- The fibres of `blockOf` on `range (∑ e)` have exactly the prescribed sizes. -/
lemma card_blockOf_fibre (hp : 0 < p) (j : Fin p) :
    ((Finset.range (∑ i, e i)).filter (fun x => blockOf e hp x = j)).card = e j := by
  have hset : (Finset.range (∑ i, e i)).filter (fun x => blockOf e hp x = j)
      = Finset.Ico (T e j.val) (T e (j.val + 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hb⟩
      exact (blockOf_eq_iff e hp hx j).mp hb
    · rintro ⟨h1, h2⟩
      have h3 : T e ((j : ℕ) + 1) ≤ ∑ i, e i := by
        rw [← T_top e]
        exact T_mono e (show (j : ℕ) + 1 ≤ p from j.isLt)
      have hx : x < ∑ i, e i := by omega
      exact ⟨hx, (blockOf_eq_iff e hp hx j).mpr ⟨h1, h2⟩⟩
  rw [hset, Nat.card_Ico, T_succ, Nat.add_sub_cancel_left]
  simp [eExt, j.isLt]

end Blocks

theorem proof :
    ∀ L : ℕ, Odd L →
      ∀ p : ℕ, ∀ e : Fin p → ℕ, (∑ j, e j) = L →
        ∃ color : Fin (L + 1) → Fin (L + 1) → Fin p,
          (∀ a b, color a b = color b a) ∧
          (∀ v : Fin (L + 1), ∀ j : Fin p,
            (Finset.univ.filter (fun u => u ≠ v ∧ color u v = j)).card = e j) := by
  intro L hL p e hsum
  have hL1 : 1 ≤ L := hL.pos
  have _ : NeZero L := NeZero.of_pos hL1
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · exfalso; subst h; simp at hsum; omega
    · exact h
  -- an inverse of 2 in `ZMod L`
  obtain ⟨i2, h2⟩ : ∃ z : ZMod L, (2 : ZMod L) * z = 1 := by
    refine ⟨(((L + 1) / 2 : ℕ) : ZMod L), ?_⟩
    have heven : (L + 1) / 2 * 2 = L + 1 := Nat.div_two_mul_two_of_even hL.add_one
    have hcast : ((((L + 1) / 2) * 2 : ℕ) : ZMod L) = ((L + 1 : ℕ) : ZMod L) := by
      rw [heven]
    push_cast at hcast
    rw [ZMod.natCast_self, zero_add] at hcast
    rw [mul_comm]
    exact hcast
  -- cancellation lemmas
  have hcancel : ∀ x y : ZMod L, x * i2 = y * i2 → x = y := by
    intro x y hxy
    have h' : x * (i2 * 2) = y * (i2 * 2) := by
      rw [← mul_assoc, ← mul_assoc, hxy]
    rwa [mul_comm i2 2, h2, mul_one, mul_one] at h'
  have hcancel2 : ∀ a b : ZMod L, 2 * a = 2 * b → a = b := by
    intro a b hab
    have h' : i2 * (2 * a) = i2 * (2 * b) := congrArg _ hab
    rwa [← mul_assoc, mul_comm i2 2, h2, one_mul, ← mul_assoc, mul_comm i2 2, h2,
      one_mul] at h'
  -- cast helpers
  have hcastval : ∀ x : ZMod L, ((x.val : ℕ) : ZMod L) = x := fun x =>
    ZMod.natCast_rightInverse x
  have hnatinj : ∀ x y : ℕ, x < L → y < L → ((x : ZMod L) = (y : ZMod L)) → x = y := by
    intro x y hx hy hxy
    have h := congrArg ZMod.val hxy
    rwa [ZMod.val_cast_of_lt hx, ZMod.val_cast_of_lt hy] at h
  -- fixed point of the affine map
  have hfix : ∀ w x : ZMod L, (x + w) * i2 = w ↔ x = w := by
    intro w x
    constructor
    · intro h
      have h' : (x + w) * i2 * 2 = w * 2 := by rw [h]
      rw [mul_assoc, mul_comm i2 2, h2, mul_one] at h'
      have h'' : x + w = w + w := by rw [h']; ring
      exact add_right_cancel h''
    · rintro rfl
      have hx : (x + x) * i2 = x * (2 * i2) := by ring
      rw [hx, h2, mul_one]
  -- the colouring
  set colr : Fin (L + 1) → Fin (L + 1) → Fin p := fun a b =>
    if (a : ℕ) < L then
      if (b : ℕ) < L then
        blockOf e hp ((((a : ℕ) : ZMod L) + ((b : ℕ) : ZMod L)) * i2).val
      else blockOf e hp (a : ℕ)
    else blockOf e hp (b : ℕ)
    with hcolr
  refine ⟨colr, ?_, ?_⟩
  · -- symmetry
    intro a b
    by_cases ha : (a : ℕ) < L <;> by_cases hb : (b : ℕ) < L
    · simp only [hcolr, if_pos ha, if_pos hb]
      rw [add_comm (((a : ℕ) : ZMod L)) (((b : ℕ) : ZMod L))]
    · simp only [hcolr, if_pos ha, if_neg hb]
    · simp only [hcolr, if_neg ha, if_pos hb]
    · have ha' : (a : ℕ) = L := by have := a.is_le; omega
      have hb' : (b : ℕ) = L := by have := b.is_le; omega
      simp only [hcolr, if_neg ha, if_neg hb, ha', hb']
  · -- regularity
    intro v j
    -- the master fibre count over `range L`
    have hcard : ((Finset.range L).filter (fun x => blockOf e hp x = j)).card = e j := by
      have h := card_blockOf_fibre e hp j
      rwa [hsum] at h
    -- fibre count over `ZMod L`
    have hgF : ((Finset.univ : Finset (ZMod L)).filter
        (fun y => blockOf e hp y.val = j)).card = e j := by
      rw [← hcard]
      apply Finset.card_bij (fun (y : ZMod L) _ => y.val)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
        exact ⟨ZMod.val_lt y, hy.2⟩
      · intro y1 _ y2 _ hval
        exact ZMod.val_injective L hval
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        refine ⟨(x : ZMod L), ?_, ZMod.val_cast_of_lt hx.1⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          ZMod.val_cast_of_lt hx.1]
        exact hx.2
    by_cases hv : (v : ℕ) < L
    · -- finite vertex
      set w : ZMod L := ((v : ℕ) : ZMod L) with hwdef
      have hwval : w.val = (v : ℕ) := ZMod.val_cast_of_lt hv
      rw [← hgF]
      apply Finset.card_bij
        (fun (u : Fin (L + 1)) _ =>
          if (u : ℕ) < L then (((u : ℕ) : ZMod L) + w) * i2 else w)
      · -- maps into the fibre
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        obtain ⟨hune, hucol⟩ := hu
        simp only [hcolr] at hucol
        by_cases huL : (u : ℕ) < L
        · rw [if_pos huL]
          rw [if_pos huL, if_pos hv] at hucol
          exact hucol
        · rw [if_neg huL]
          rw [if_neg huL] at hucol
          rwa [hwval]
      · -- injective
        intro u1 hu1 u2 hu2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
        by_cases h1 : (u1 : ℕ) < L <;> by_cases h2' : (u2 : ℕ) < L
        · rw [if_pos h1, if_pos h2'] at heq
          have ha := hcancel _ _ heq
          have hb := add_right_cancel ha
          exact Fin.ext (hnatinj _ _ h1 h2' hb)
        · rw [if_pos h1, if_neg h2'] at heq
          exfalso
          have hfx := (hfix w _).mp heq
          have hval : (u1 : ℕ) = (v : ℕ) := hnatinj _ _ h1 hv hfx
          exact hu1.1 (Fin.ext hval)
        · rw [if_neg h1, if_pos h2'] at heq
          exfalso
          have hfx := (hfix w _).mp heq.symm
          have hval : (u2 : ℕ) = (v : ℕ) := hnatinj _ _ h2' hv hfx
          exact hu2.1 (Fin.ext hval)
        · have e1 : (u1 : ℕ) = L := by have := u1.is_le; omega
          have e2 : (u2 : ℕ) = L := by have := u2.is_le; omega
          exact Fin.ext (e1.trans e2.symm)
      · -- surjective
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_cases hyw : y = w
        · -- take u = the vertex at infinity
          have hLlt : L < L + 1 := Nat.lt_succ_self L
          refine ⟨⟨L, hLlt⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h
              have hval : L = (v : ℕ) := congrArg Fin.val h
              omega
            · simp only [hcolr]
              rw [if_neg (lt_irrefl L), ← hwval, ← hyw]
              exact hy
          · have hmk : ((⟨L, hLlt⟩ : Fin (L + 1)) : ℕ) = L := rfl
            rw [hmk, if_neg (lt_irrefl L)]
            exact hyw.symm
        · -- take u with `(u : ZMod L) = 2 * y - w`
          set x : ZMod L := 2 * y - w with hxdef
          have hxy : (x + w) * i2 = y := by
            rw [hxdef]
            have hr : (2 * y - w + w) * i2 = y * (2 * i2) := by ring
            rw [hr, h2, mul_one]
          have hxne : x ≠ w := by
            intro hxw
            apply hyw
            apply hcancel2
            have hw' : 2 * y - w = w := hxdef.symm.trans hxw
            have h'' : 2 * y = w + w := sub_eq_iff_eq_add.mp hw'
            rw [h'']; ring
          have hxval : x.val < L := ZMod.val_lt x
          have hult : x.val < L + 1 := by omega
          have hmk : ((⟨x.val, hult⟩ : Fin (L + 1)) : ℕ) = x.val := rfl
          refine ⟨⟨x.val, hult⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h
              apply hxne
              have hvv : x.val = (v : ℕ) := congrArg Fin.val h
              rw [← hcastval x, hvv, hwdef]
            · simp only [hcolr]
              rw [if_pos hxval, if_pos hv, hcastval x, ← hwdef, hxy]
              exact hy
          · rw [hmk, if_pos hxval, hcastval x]
            exact hxy
    · -- vertex at infinity
      have hvL : (v : ℕ) = L := by have := v.is_le; omega
      rw [← hcard]
      apply Finset.card_bij (fun (u : Fin (L + 1)) _ => (u : ℕ))
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨hune, hucol⟩ := hu
        have huL : (u : ℕ) < L := by
          rcases lt_or_eq_of_le u.is_le with h | h
          · exact h
          · exact absurd (Fin.ext (h.trans hvL.symm)) hune
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨huL, ?_⟩
        simp only [hcolr] at hucol
        rw [if_pos huL, if_neg hv] at hucol
        exact hucol
      · intro u1 _ u2 _ hval
        exact Fin.ext hval
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        have hxlt : x < L + 1 := by omega
        have hmk : ((⟨x, hxlt⟩ : Fin (L + 1)) : ℕ) = x := rfl
        refine ⟨⟨x, hxlt⟩, ?_, hmk⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          have hval : x = (v : ℕ) := congrArg Fin.val h
          omega
        · simp only [hcolr]
          rw [if_pos hx.1, if_neg hv]
          exact hx.2

end Submissions.RoundRobinRegularDecomposition.RoundRobin
