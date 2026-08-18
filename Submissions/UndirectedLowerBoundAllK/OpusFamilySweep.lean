import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
Currie–Mol Theorem 3, complete. One certificate lemma (`gen`), one counting lemma (`cover`),
and three trees: the uniform one at `k = q + 6` (`thm3`), and the bespoke ones at `k = 5`
(`thm5`) and `k = 4` (`thm4`). `bound_of_none` turns "no infinite word is undirected `c`-free"
into `c ≤ URT k`, using that `{r | Avoidable k r}` is nonempty because no word is an undirected
`s`-power for `s ≥ 3`.

Controls, provable as NEGATIONS against these definitions: the two side conditions are tight —
at `m = 2k−5` and at `d = k−1` the exponent inequality `r(l+m) ≤ 2l+m` is false.
-/

namespace Submissions.UndirectedLowerBoundAllK.OpusFamilySweep
variable {α : Type*}

def IsUndirectedPower (r : ℝ) (z : List α) : Prop :=
  ∃ x y x' : List α,
    z = x ++ y ++ x' ∧ x ≠ [] ∧ (x' = x ∨ x' = x.reverse) ∧
      (z.length : ℝ) = r * ((x ++ y).length : ℝ)

def factor (w : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => w (i + j)

def UndirectedFree (r : ℝ) (w : ℕ → α) : Prop :=
  ∀ (i n : ℕ) (s : ℝ), r ≤ s → ¬ IsUndirectedPower s (factor w i n)

def Avoidable (k : ℕ) (r : ℝ) : Prop := ∃ w : ℕ → Fin k, UndirectedFree r w

noncomputable def URT (k : ℕ) : ℝ := sInf {r : ℝ | Avoidable k r}


/-- The canonical proposition: Currie–Mol's Theorem 3, in full — the proved half of their
Conjecture 1, for every `k ≥ 4`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k → ((k : ℝ) - 1) / ((k : ℝ) - 2) ≤ URT k
theorem factor_add (w : ℕ → α) (i a b : ℕ) :
    factor w i (a + b) = factor w i a ++ factor w (i + a) b := by
  simp [factor, List.range_add, List.map_append, List.map_map, Function.comp,
    Nat.add_comm, Nat.add_left_comm]

theorem factor_length (w : ℕ → α) (i n : ℕ) : (factor w i n).length = n := by simp [factor]
theorem factor_one (w : ℕ → α) (i : ℕ) : factor w i 1 = [w i] := by simp [factor]
theorem factor_two (w : ℕ → α) (i : ℕ) : factor w i 2 = [w i, w (i + 1)] := by
  simp [factor, List.range_succ]

theorem gen {k : ℕ} (w : ℕ → Fin k) (r : ℝ) (hf : UndirectedFree r w)
    (i l m : ℕ) (hl : 1 ≤ l) (hexp : r * ((l : ℝ) + (m : ℝ)) ≤ 2 * (l : ℝ) + (m : ℝ)) :
    factor w (i + l + m) l ≠ factor w i l ∧
    factor w (i + l + m) l ≠ (factor w i l).reverse := by
  have hlR : (1:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have hlm : (0:ℝ) < ((l:ℝ) + (m:ℝ)) := by positivity
  set s : ℝ := (2 * (l:ℝ) + (m:ℝ)) / ((l:ℝ) + (m:ℝ)) with hsdef
  have hs : r ≤ s := by rw [hsdef, le_div_iff₀ hlm]; linarith
  have main : ¬ (factor w (i + l + m) l = factor w i l ∨
      factor w (i + l + m) l = (factor w i l).reverse) := by
    intro h
    refine hf i (2 * l + m) s hs ?_
    refine ⟨factor w i l, factor w (i + l) m, factor w (i + l + m) l, ?_, ?_, h, ?_⟩
    · have e : 2 * l + m = l + (m + l) := by ring
      rw [e, factor_add, factor_add, ← List.append_assoc]
    · intro hc
      have h2 := factor_length w i l
      rw [hc] at h2
      simp at h2
      omega
    · rw [factor_length, List.length_append, factor_length, factor_length, hsdef]
      push_cast; field_simp
  exact ⟨fun h => main (Or.inl h), fun h => main (Or.inr h)⟩

theorem cover {n : ℕ} (w : ℕ → Fin (n + 1)) (mu : Fin (n + 1))
    (hinj : ∀ i j, i < n → j < n → w i = w j → i = j)
    (hmu : ∀ j, j < n → mu ≠ w j) :
    ∀ x : Fin (n + 1), x = mu ∨ ∃ j, j < n ∧ x = w j := by
  have hnd : ((List.range n).map w).Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro x hx y hy hxy
    exact hinj x y (List.mem_range.1 hx) (List.mem_range.1 hy) hxy
  have hL : (mu :: (List.range n).map w).Nodup := by
    refine List.nodup_cons.2 ⟨?_, hnd⟩
    intro hc
    obtain ⟨j, hj, hje⟩ := List.mem_map.1 hc
    exact hmu j (List.mem_range.1 hj) hje.symm
  have hcard : (mu :: (List.range n).map w).toFinset.card = Fintype.card (Fin (n + 1)) := by
    rw [List.toFinset_card_of_nodup hL, Fintype.card_fin]; simp
  have huniv : (mu :: (List.range n).map w).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  intro x
  have hx : x ∈ (mu :: (List.range n).map w) := by
    have : x ∈ (mu :: (List.range n).map w).toFinset := by rw [huniv]; exact Finset.mem_univ x
    exact List.mem_toFinset.1 this
  rcases List.mem_cons.1 hx with h | h
  · exact Or.inl h
  · obtain ⟨j, hj, hje⟩ := List.mem_map.1 h
    exact Or.inr ⟨j, List.mem_range.1 hj, hje.symm⟩


theorem thm3 (q : ℕ) (w : ℕ → Fin (q + 6))
    (hf : UndirectedFree ((((q:ℝ) + 6) - 1) / (((q:ℝ) + 6) - 2)) w) : False := by
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  have hK2 : (0:ℝ) < ((q:ℝ) + 6) - 2 := by linarith
  -- l = 1 : two equal letters must be at distance ≥ k-1
  have dist : ∀ i d : ℕ, 1 ≤ d → d ≤ q + 4 → w i ≠ w (i + d) := by
    intro i d hd hdk
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : (e:ℝ) + 1 ≤ (q:ℝ) + 4 := by exact_mod_cast (by omega : e + 1 ≤ q + 4)
    have h := (gen w _ hf i 1 e le_rfl (by
      push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ hK2]
      nlinarith)).1
    intro hc
    exact h (by rw [factor_one, factor_one, show i + 1 + e = i + (e+1) from by omega, hc])
  have ne2 : ∀ i j : ℕ, i < j → j ≤ i + (q+4) → w i ≠ w j := by
    intro i j hij hjk
    have h := dist i (j - i) (by omega) (by omega)
    rwa [show i + (j - i) = j from by omega] at h
  -- l = 2 : an adjacent pair may not reoccur, in either order, after a gap ≤ 2k-6
  have pf : ∀ i m : ℕ, m ≤ 2*q + 6 → ¬ (w (i+2+m) = w i ∧ w (i+3+m) = w (i+1)) := by
    rintro i m hm ⟨h1, h2⟩
    have hmR : (m:ℝ) ≤ 2*(q:ℝ) + 6 := by exact_mod_cast hm
    exact (gen w _ hf i 2 m (by omega) (by
      push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ hK2]
      nlinarith)).1
      (by rw [factor_two, factor_two, show i+2+m+1 = i+3+m from by omega, h1, h2])
  have pr : ∀ i m : ℕ, m ≤ 2*q + 6 → ¬ (w (i+2+m) = w (i+1) ∧ w (i+3+m) = w i) := by
    rintro i m hm ⟨h1, h2⟩
    have hmR : (m:ℝ) ≤ 2*(q:ℝ) + 6 := by exact_mod_cast hm
    exact (gen w _ hf i 2 m (by omega) (by
      push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ hK2]
      nlinarith)).2
      (by rw [factor_two, factor_two, show i+2+m+1 = i+3+m from by omega, h1, h2]; simp)
  have hinj : ∀ i j, i < q+5 → j < q+5 → w i = w j → i = j := by
    intro i j hi hj he
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact ne2 i j h (by omega) he
    · exact ne2 j i (by omega) (by omega) he.symm
  have pick : ∀ (mu : Fin (q+6)), (∀ j, j < q+5 → mu ≠ w j) → ∀ (n lo : ℕ),
      lo + (q+4) = n → q + 5 ≤ n → w n ≠ mu → ∃ j, j < lo ∧ w n = w j := by
    intro mu hmu n lo hlo hn hne
    rcases cover (n := q+5) w mu hinj hmu (w n) with h | ⟨j, hj, hje⟩
    · exact absurd h hne
    · refine ⟨j, ?_, hje⟩
      by_contra hc
      push_neg at hc
      exact (ne2 j n (by omega) (by omega)) hje.symm
  by_cases hA : w (q+5) = w 0
  · by_cases hA1 : w (q+6) = w 1
    · exact pf 0 (q+3) (by omega) ⟨by rw [show 0+2+(q+3) = q+5 from by omega]; exact hA,
        by rw [show 0+3+(q+3) = q+6 from by omega]; exact hA1⟩
    · have hmu : ∀ j, j < q+5 → w (q+6) ≠ w j := by
        intro j hj
        rcases j with _ | _ | j
        · intro hc; exact (ne2 (q+5) (q+6) (by omega) (by omega)) (by rw [hA, hc])
        · exact hA1
        · exact (ne2 _ (q+6) (by omega) (by omega)).symm
      have hne6 : w (q+6) ≠ w (q+5) := (ne2 (q+5) (q+6) (by omega) (by omega)).symm
      have h7 : w (q+7) = w 1 ∨ w (q+7) = w 2 := by
        obtain ⟨j, hj, hje⟩ := pick (w (q+6)) hmu (q+7) 3 (by omega) (by omega)
          (ne2 (q+6) (q+7) (by omega) (by omega)).symm
        interval_cases j
        · exact absurd (show w (q+7) = w (q+5) by rw [hje, ← hA])
            (ne2 (q+5) (q+7) (by omega) (by omega)).symm
        · exact Or.inl hje
        · exact Or.inr hje
      rcases h7 with h7 | h7
      · have h8 : w (q+8) = w 2 ∨ w (q+8) = w 3 := by
          obtain ⟨j, hj, hje⟩ := pick (w (q+6)) hmu (q+8) 4 (by omega) (by omega)
            (ne2 (q+6) (q+8) (by omega) (by omega)).symm
          interval_cases j
          · exact absurd (show w (q+8) = w (q+5) by rw [hje, ← hA])
              (ne2 (q+5) (q+8) (by omega) (by omega)).symm
          · exact absurd (show w (q+8) = w (q+7) by rw [hje, ← h7])
              (ne2 (q+7) (q+8) (by omega) (by omega)).symm
          · exact Or.inl hje
          · exact Or.inr hje
        rcases h8 with h8 | h8
        · exact pf 1 (q+4) (by omega) ⟨by rw [show 1+2+(q+4) = q+7 from by omega]; exact h7,
            by rw [show 1+3+(q+4) = q+8 from by omega]; exact h8⟩
        · have h9 : w (q+9) = w 2 ∨ w (q+9) = w 4 := by
            obtain ⟨j, hj, hje⟩ := pick (w (q+6)) hmu (q+9) 5 (by omega) (by omega)
              (ne2 (q+6) (q+9) (by omega) (by omega)).symm
            interval_cases j
            · exact absurd (show w (q+9) = w (q+5) by rw [hje, ← hA])
                (ne2 (q+5) (q+9) (by omega) (by omega)).symm
            · exact absurd (show w (q+9) = w (q+7) by rw [hje, ← h7])
                (ne2 (q+7) (q+9) (by omega) (by omega)).symm
            · exact Or.inl hje
            · exact absurd (show w (q+9) = w (q+8) by rw [hje, ← h8])
                (ne2 (q+8) (q+9) (by omega) (by omega)).symm
            · exact Or.inr hje
          rcases h9 with h9 | h9
          · exact pr 2 (q+4) (by omega) ⟨by rw [show 2+2+(q+4) = q+8 from by omega]; exact h8,
              by rw [show 2+3+(q+4) = q+9 from by omega]; exact h9⟩
          · exact pf 3 (q+3) (by omega) ⟨by rw [show 3+2+(q+3) = q+8 from by omega]; exact h8,
              by rw [show 3+3+(q+3) = q+9 from by omega]; exact h9⟩
      · have h8 : w (q+8) = w 1 ∨ w (q+8) = w 3 := by
          obtain ⟨j, hj, hje⟩ := pick (w (q+6)) hmu (q+8) 4 (by omega) (by omega)
            (ne2 (q+6) (q+8) (by omega) (by omega)).symm
          interval_cases j
          · exact absurd (show w (q+8) = w (q+5) by rw [hje, ← hA])
              (ne2 (q+5) (q+8) (by omega) (by omega)).symm
          · exact Or.inl hje
          · exact absurd (show w (q+8) = w (q+7) by rw [hje, ← h7])
              (ne2 (q+7) (q+8) (by omega) (by omega)).symm
          · exact Or.inr hje
        rcases h8 with h8 | h8
        · exact pr 1 (q+4) (by omega) ⟨by rw [show 1+2+(q+4) = q+7 from by omega]; exact h7,
            by rw [show 1+3+(q+4) = q+8 from by omega]; exact h8⟩
        · exact pf 2 (q+3) (by omega) ⟨by rw [show 2+2+(q+3) = q+7 from by omega]; exact h7,
            by rw [show 2+3+(q+3) = q+8 from by omega]; exact h8⟩
  · have hmu : ∀ j, j < q+5 → w (q+5) ≠ w j := by
      intro j hj
      rcases j with _ | j
      · exact hA
      · exact (ne2 _ (q+5) (by omega) (by omega)).symm
    have h6 : w (q+6) = w 0 ∨ w (q+6) = w 1 := by
      obtain ⟨j, hj, hje⟩ := pick (w (q+5)) hmu (q+6) 2 (by omega) (by omega)
        (ne2 (q+5) (q+6) (by omega) (by omega)).symm
      interval_cases j
      · exact Or.inl hje
      · exact Or.inr hje
    rcases h6 with h6 | h6
    · have h7 : w (q+7) = w 1 ∨ w (q+7) = w 2 := by
        obtain ⟨j, hj, hje⟩ := pick (w (q+5)) hmu (q+7) 3 (by omega) (by omega)
          (ne2 (q+5) (q+7) (by omega) (by omega)).symm
        interval_cases j
        · exact absurd (show w (q+7) = w (q+6) by rw [hje, ← h6])
            (ne2 (q+6) (q+7) (by omega) (by omega)).symm
        · exact Or.inl hje
        · exact Or.inr hje
      rcases h7 with h7 | h7
      · exact pf 0 (q+4) (by omega) ⟨by rw [show 0+2+(q+4) = q+6 from by omega]; exact h6,
          by rw [show 0+3+(q+4) = q+7 from by omega]; exact h7⟩
      · have h8 : w (q+8) = w 1 ∨ w (q+8) = w 3 := by
          obtain ⟨j, hj, hje⟩ := pick (w (q+5)) hmu (q+8) 4 (by omega) (by omega)
            (ne2 (q+5) (q+8) (by omega) (by omega)).symm
          interval_cases j
          · exact absurd (show w (q+8) = w (q+6) by rw [hje, ← h6])
              (ne2 (q+6) (q+8) (by omega) (by omega)).symm
          · exact Or.inl hje
          · exact absurd (show w (q+8) = w (q+7) by rw [hje, ← h7])
              (ne2 (q+7) (q+8) (by omega) (by omega)).symm
          · exact Or.inr hje
        rcases h8 with h8 | h8
        · exact pr 1 (q+4) (by omega) ⟨by rw [show 1+2+(q+4) = q+7 from by omega]; exact h7,
            by rw [show 1+3+(q+4) = q+8 from by omega]; exact h8⟩
        · exact pf 2 (q+3) (by omega) ⟨by rw [show 2+2+(q+3) = q+7 from by omega]; exact h7,
            by rw [show 2+3+(q+3) = q+8 from by omega]; exact h8⟩
    · have h7 : w (q+7) = w 0 ∨ w (q+7) = w 2 := by
        obtain ⟨j, hj, hje⟩ := pick (w (q+5)) hmu (q+7) 3 (by omega) (by omega)
          (ne2 (q+5) (q+7) (by omega) (by omega)).symm
        interval_cases j
        · exact Or.inl hje
        · exact absurd (show w (q+7) = w (q+6) by rw [hje, ← h6])
            (ne2 (q+6) (q+7) (by omega) (by omega)).symm
        · exact Or.inr hje
      rcases h7 with h7 | h7
      · exact pr 0 (q+4) (by omega) ⟨by rw [show 0+2+(q+4) = q+6 from by omega]; exact h6,
          by rw [show 0+3+(q+4) = q+7 from by omega]; exact h7⟩
      · exact pf 1 (q+3) (by omega) ⟨by rw [show 1+2+(q+3) = q+6 from by omega]; exact h6,
          by rw [show 1+3+(q+3) = q+7 from by omega]; exact h7⟩



theorem no_big_power {k : ℕ} (s : ℝ) (hs : 3 ≤ s) (z : List (Fin k)) :
    ¬ IsUndirectedPower s z := by
  rintro ⟨x, y, x', hz, hx, hxx, hlen⟩
  have hxl : 1 ≤ (x.length : ℝ) := by
    have : 1 ≤ x.length := List.length_pos_iff.2 hx
    exact_mod_cast this
  have hxy : (0:ℝ) < ((x ++ y).length : ℝ) := by
    rw [List.length_append]; push_cast; have : (0:ℝ) ≤ (y.length : ℝ) := by positivity
    linarith
  have hx'l : x'.length = x.length := by
    rcases hxx with h | h
    · rw [h]
    · rw [h, List.length_reverse]
  have hzl : (z.length : ℝ) = 2 * (x.length : ℝ) + (y.length : ℝ) := by
    rw [hz]; simp [List.length_append, hx'l]; push_cast; ring
  rw [hzl, List.length_append] at hlen
  push_cast at hlen
  nlinarith [hlen, hs, hxl, hxy, (by positivity : (0:ℝ) ≤ (y.length:ℝ))]

theorem lower_bound (k : ℕ) (hk : 6 ≤ k) : ((k : ℝ) - 1) / ((k : ℝ) - 2) ≤ URT k := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 6 := ⟨k - 6, by omega⟩
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  have hcast : ((q + 6 : ℕ) : ℝ) = (q:ℝ) + 6 := by push_cast; ring
  have hne : ({r : ℝ | Avoidable (q+6) r}).Nonempty := by
    refine ⟨3, ⟨fun _ => ⟨0, by omega⟩, ?_⟩⟩
    intro i n s hs
    exact no_big_power s hs _
  refine le_csInf hne ?_
  rintro r ⟨w, hw⟩
  by_contra hlt
  push_neg at hlt
  refine thm3 q w ?_
  intro i n s hs
  refine hw i n s ?_
  rw [hcast] at hlt
  linarith


theorem thm5 (w : ℕ → Fin 5) (hf : UndirectedFree (((5:ℝ) - 1) / ((5:ℝ) - 2)) w) : False := by
  have dist : ∀ i d : ℕ, 1 ≤ d → d ≤ 3 → w i ≠ w (i + d) := by
    intro i d hd hdk
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : (e:ℝ) + 1 ≤ 3 := by exact_mod_cast (by omega : e + 1 ≤ 3)
    have h := (gen w _ hf i 1 e le_rfl (by push_cast; norm_num; linarith)).1
    intro hc
    exact h (by rw [factor_one, factor_one, show i + 1 + e = i + (e+1) from by omega, hc])
  have ne2 : ∀ i j : ℕ, i < j → j ≤ i + 3 → w i ≠ w j := by
    intro i j hij hjk
    have h := dist i (j - i) (by omega) (by omega)
    rwa [show i + (j - i) = j from by omega] at h
  have pf : ∀ i m : ℕ, m ≤ 4 → ¬ (w (i+2+m) = w i ∧ w (i+3+m) = w (i+1)) := by
    rintro i m hm ⟨h1, h2⟩
    have hmR : (m:ℝ) ≤ 4 := by exact_mod_cast hm
    exact (gen w _ hf i 2 m (by omega) (by push_cast; norm_num; linarith)).1
      (by rw [factor_two, factor_two, show i+2+m+1 = i+3+m from by omega, h1, h2])
  have pr : ∀ i m : ℕ, m ≤ 4 → ¬ (w (i+2+m) = w (i+1) ∧ w (i+3+m) = w i) := by
    rintro i m hm ⟨h1, h2⟩
    have hmR : (m:ℝ) ≤ 4 := by exact_mod_cast hm
    exact (gen w _ hf i 2 m (by omega) (by push_cast; norm_num; linarith)).2
      (by rw [factor_two, factor_two, show i+2+m+1 = i+3+m from by omega, h1, h2]; simp)
  have hinj : ∀ i j, i < 4 → j < 4 → w i = w j → i = j := by
    intro i j hi hj he
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact ne2 i j h (by omega) he
    · exact ne2 j i (by omega) (by omega) he.symm
  have pick : ∀ (mu : Fin 5), (∀ j, j < 4 → mu ≠ w j) → ∀ (n lo : ℕ),
      lo + 3 = n → 4 ≤ n → w n ≠ mu → ∃ j, j < lo ∧ w n = w j := by
    intro mu hmu n lo hlo hn hne
    rcases cover (n := 4) w mu hinj hmu (w n) with h | ⟨j, hj, hje⟩
    · exact absurd h hne
    · refine ⟨j, ?_, hje⟩
      by_contra hc
      push_neg at hc
      exact (ne2 j n (by omega) (by omega)) hje.symm
  by_cases hA : w 4 = w 0
  · by_cases hA1 : w 5 = w 1
    · exact pf 0 2 (by omega) ⟨hA, hA1⟩
    · have hmu : ∀ j, j < 4 → w 5 ≠ w j := by
        intro j hj
        rcases j with _ | _ | j
        · intro hc; exact (ne2 4 5 (by omega) (by omega)) (by rw [hA, hc])
        · exact hA1
        · exact (ne2 _ 5 (by omega) (by omega)).symm
      have h6 : w 6 = w 1 ∨ w 6 = w 2 := by
        obtain ⟨j, hj, hje⟩ := pick (w 5) hmu 6 3 (by omega) (by omega)
          (ne2 5 6 (by omega) (by omega)).symm
        interval_cases j
        · exact absurd (show w 6 = w 4 by rw [hje, ← hA]) (ne2 4 6 (by omega) (by omega)).symm
        · exact Or.inl hje
        · exact Or.inr hje
      rcases h6 with h6 | h6
      · have h7 : w 7 = w 2 ∨ w 7 = w 3 := by
          obtain ⟨j, hj, hje⟩ := pick (w 5) hmu 7 4 (by omega) (by omega)
            (ne2 5 7 (by omega) (by omega)).symm
          interval_cases j
          · exact absurd (show w 7 = w 4 by rw [hje, ← hA]) (ne2 4 7 (by omega) (by omega)).symm
          · exact absurd (show w 7 = w 6 by rw [hje, ← h6]) (ne2 6 7 (by omega) (by omega)).symm
          · exact Or.inl hje
          · exact Or.inr hje
        rcases h7 with h7 | h7
        · exact pf 1 3 (by omega) ⟨h6, h7⟩
        · have h8 : w 8 = w 0 ∨ w 8 = w 2 := by
            obtain ⟨j, hj, hje⟩ := pick (w 5) hmu 8 5 (by omega) (by omega)
              (ne2 5 8 (by omega) (by omega)).symm
            interval_cases j
            · exact Or.inl hje
            · exact absurd (show w 8 = w 6 by rw [hje, ← h6]) (ne2 6 8 (by omega) (by omega)).symm
            · exact Or.inr hje
            · exact absurd (show w 8 = w 7 by rw [hje, ← h7]) (ne2 7 8 (by omega) (by omega)).symm
            · exact Or.inl (hje.trans hA)
          rcases h8 with h8 | h8
          · exact pf 3 2 (by omega) ⟨h7, h8.trans hA.symm⟩
          · exact pr 2 3 (by omega) ⟨h7, h8⟩
      · have h7 : w 7 = w 1 ∨ w 7 = w 3 := by
          obtain ⟨j, hj, hje⟩ := pick (w 5) hmu 7 4 (by omega) (by omega)
            (ne2 5 7 (by omega) (by omega)).symm
          interval_cases j
          · exact absurd (show w 7 = w 4 by rw [hje, ← hA]) (ne2 4 7 (by omega) (by omega)).symm
          · exact Or.inl hje
          · exact absurd (show w 7 = w 6 by rw [hje, ← h6]) (ne2 6 7 (by omega) (by omega)).symm
          · exact Or.inr hje
        rcases h7 with h7 | h7
        · exact pr 1 3 (by omega) ⟨h6, h7⟩
        · exact pf 2 2 (by omega) ⟨h6, h7⟩
  · have hmu : ∀ j, j < 4 → w 4 ≠ w j := by
      intro j hj
      rcases j with _ | j
      · exact hA
      · exact (ne2 _ 4 (by omega) (by omega)).symm
    have h5 : w 5 = w 0 ∨ w 5 = w 1 := by
      obtain ⟨j, hj, hje⟩ := pick (w 4) hmu 5 2 (by omega) (by omega)
        (ne2 4 5 (by omega) (by omega)).symm
      interval_cases j
      · exact Or.inl hje
      · exact Or.inr hje
    rcases h5 with h5 | h5
    · have h6 : w 6 = w 1 ∨ w 6 = w 2 := by
        obtain ⟨j, hj, hje⟩ := pick (w 4) hmu 6 3 (by omega) (by omega)
          (ne2 4 6 (by omega) (by omega)).symm
        interval_cases j
        · exact absurd (show w 6 = w 5 by rw [hje, ← h5]) (ne2 5 6 (by omega) (by omega)).symm
        · exact Or.inl hje
        · exact Or.inr hje
      rcases h6 with h6 | h6
      · exact pf 0 3 (by omega) ⟨h5, h6⟩
      · have h7 : w 7 = w 1 ∨ w 7 = w 3 := by
          obtain ⟨j, hj, hje⟩ := pick (w 4) hmu 7 4 (by omega) (by omega)
            (ne2 4 7 (by omega) (by omega)).symm
          interval_cases j
          · exact absurd (show w 7 = w 5 by rw [hje, ← h5]) (ne2 5 7 (by omega) (by omega)).symm
          · exact Or.inl hje
          · exact absurd (show w 7 = w 6 by rw [hje, ← h6]) (ne2 6 7 (by omega) (by omega)).symm
          · exact Or.inr hje
        rcases h7 with h7 | h7
        · exact pr 1 3 (by omega) ⟨h6, h7⟩
        · exact pf 2 2 (by omega) ⟨h6, h7⟩
    · have h6 : w 6 = w 0 ∨ w 6 = w 2 := by
        obtain ⟨j, hj, hje⟩ := pick (w 4) hmu 6 3 (by omega) (by omega)
          (ne2 4 6 (by omega) (by omega)).symm
        interval_cases j
        · exact Or.inl hje
        · exact absurd (show w 6 = w 5 by rw [hje, ← h5]) (ne2 5 6 (by omega) (by omega)).symm
        · exact Or.inr hje
      rcases h6 with h6 | h6
      · exact pr 0 3 (by omega) ⟨h5, h6⟩
      · exact pf 1 2 (by omega) ⟨h5, h6⟩


theorem thm4 (w : ℕ → Fin 4) (hf : UndirectedFree (((4:ℝ) - 1) / ((4:ℝ) - 2)) w) : False := by
  have dist : ∀ i d : ℕ, 1 ≤ d → d ≤ 2 → w i ≠ w (i + d) := by
    intro i d hd hdk
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : (e:ℝ) + 1 ≤ 2 := by exact_mod_cast (by omega : e + 1 ≤ 2)
    have h := (gen w _ hf i 1 e le_rfl (by push_cast; norm_num; linarith)).1
    intro hc
    exact h (by rw [factor_one, factor_one, show i + 1 + e = i + (e+1) from by omega, hc])
  have ne2 : ∀ i j : ℕ, i < j → j ≤ i + 2 → w i ≠ w j := by
    intro i j hij hjk
    have h := dist i (j - i) (by omega) (by omega)
    rwa [show i + (j - i) = j from by omega] at h
  have pf : ∀ i m : ℕ, m ≤ 2 → ¬ (w (i+2+m) = w i ∧ w (i+3+m) = w (i+1)) := by
    rintro i m hm ⟨h1, h2⟩
    have hmR : (m:ℝ) ≤ 2 := by exact_mod_cast hm
    exact (gen w _ hf i 2 m (by omega) (by push_cast; norm_num; linarith)).1
      (by rw [factor_two, factor_two, show i+2+m+1 = i+3+m from by omega, h1, h2])
  have pr : ∀ i m : ℕ, m ≤ 2 → ¬ (w (i+2+m) = w (i+1) ∧ w (i+3+m) = w i) := by
    rintro i m hm ⟨h1, h2⟩
    have hmR : (m:ℝ) ≤ 2 := by exact_mod_cast hm
    exact (gen w _ hf i 2 m (by omega) (by push_cast; norm_num; linarith)).2
      (by rw [factor_two, factor_two, show i+2+m+1 = i+3+m from by omega, h1, h2]; simp)
  have hinj : ∀ i j, i < 3 → j < 3 → w i = w j → i = j := by
    intro i j hi hj he
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact ne2 i j h (by omega) he
    · exact ne2 j i (by omega) (by omega) he.symm
  by_cases hA : w 3 = w 0
  · by_cases hA1 : w 4 = w 1
    · exact pf 0 1 (by omega) ⟨hA, hA1⟩
    · have hmu : ∀ j, j < 3 → w 4 ≠ w j := by
        intro j hj
        rcases j with _ | _ | j
        · intro hc; exact (ne2 3 4 (by omega) (by omega)) (by rw [hA, hc])
        · exact hA1
        · exact (ne2 _ 4 (by omega) (by omega)).symm
      have cov := cover (n := 3) w (w 4) hinj hmu
      have h5 : w 5 = w 1 ∨ w 5 = w 2 := by
        rcases cov (w 5) with h | ⟨j, hj, hje⟩
        · exact absurd h (ne2 4 5 (by omega) (by omega)).symm
        · interval_cases j
          · exact absurd (show w 3 = w 5 by rw [hA, ← hje]) (ne2 3 5 (by omega) (by omega))
          · exact Or.inl hje
          · exact Or.inr hje
      rcases h5 with h5 | h5
      · have h6 : w 6 = w 3 ∨ w 6 = w 2 := by
          rcases cov (w 6) with h | ⟨j, hj, hje⟩
          · exact absurd h (ne2 4 6 (by omega) (by omega)).symm
          · interval_cases j
            · exact Or.inl (hje.trans hA.symm)
            · exact absurd (show w 5 = w 6 by rw [h5, ← hje]) (ne2 5 6 (by omega) (by omega))
            · exact Or.inr hje
        rcases h6 with h6 | h6
        · have h7 : w 7 = w 4 ∨ w 7 = w 2 := by
            rcases cov (w 7) with h | ⟨j, hj, hje⟩
            · exact Or.inl h
            · interval_cases j
              · exact absurd (show w 6 = w 7 by rw [h6, hA, ← hje]) (ne2 6 7 (by omega) (by omega))
              · exact absurd (show w 5 = w 7 by rw [h5, ← hje]) (ne2 5 7 (by omega) (by omega))
              · exact Or.inr hje
          rcases h7 with h7 | h7
          · exact pf 3 1 (by omega) ⟨h6, h7⟩
          · exact pr 2 2 (by omega) ⟨h6, h7⟩
        · exact pf 1 2 (by omega) ⟨h5, h6⟩
      · have h6 : w 6 = w 3 ∨ w 6 = w 1 := by
          rcases cov (w 6) with h | ⟨j, hj, hje⟩
          · exact absurd h (ne2 4 6 (by omega) (by omega)).symm
          · interval_cases j
            · exact Or.inl (hje.trans hA.symm)
            · exact Or.inr hje
            · exact absurd (show w 5 = w 6 by rw [h5, ← hje]) (ne2 5 6 (by omega) (by omega))
        rcases h6 with h6 | h6
        · exact pf 2 1 (by omega) ⟨h5, h6⟩
        · exact pr 1 2 (by omega) ⟨h5, h6⟩
  · have hmu : ∀ j, j < 3 → w 3 ≠ w j := by
      intro j hj
      rcases j with _ | j
      · exact hA
      · exact (ne2 _ 3 (by omega) (by omega)).symm
    have cov := cover (n := 3) w (w 3) hinj hmu
    have h4 : w 4 = w 0 ∨ w 4 = w 1 := by
      rcases cov (w 4) with h | ⟨j, hj, hje⟩
      · exact absurd h (ne2 3 4 (by omega) (by omega)).symm
      · interval_cases j
        · exact Or.inl hje
        · exact Or.inr hje
        · exact absurd (show w 2 = w 4 by rw [← hje]) (ne2 2 4 (by omega) (by omega))
    rcases h4 with h4 | h4
    · have h5 : w 5 = w 1 ∨ w 5 = w 2 := by
        rcases cov (w 5) with h | ⟨j, hj, hje⟩
        · exact absurd h (ne2 3 5 (by omega) (by omega)).symm
        · interval_cases j
          · exact absurd (show w 4 = w 5 by rw [h4, ← hje]) (ne2 4 5 (by omega) (by omega))
          · exact Or.inl hje
          · exact Or.inr hje
      rcases h5 with h5 | h5
      · exact pf 0 2 (by omega) ⟨h4, h5⟩
      · have h6 : w 6 = w 3 ∨ w 6 = w 1 := by
          rcases cov (w 6) with h | ⟨j, hj, hje⟩
          · exact Or.inl h
          · interval_cases j
            · exact absurd (show w 4 = w 6 by rw [h4, ← hje]) (ne2 4 6 (by omega) (by omega))
            · exact Or.inr hje
            · exact absurd (show w 5 = w 6 by rw [h5, ← hje]) (ne2 5 6 (by omega) (by omega))
        rcases h6 with h6 | h6
        · exact pf 2 1 (by omega) ⟨h5, h6⟩
        · exact pr 1 2 (by omega) ⟨h5, h6⟩
    · have h5 : w 5 = w 0 ∨ w 5 = w 2 := by
        rcases cov (w 5) with h | ⟨j, hj, hje⟩
        · exact absurd h (ne2 3 5 (by omega) (by omega)).symm
        · interval_cases j
          · exact Or.inl hje
          · exact absurd (show w 4 = w 5 by rw [h4, ← hje]) (ne2 4 5 (by omega) (by omega))
          · exact Or.inr hje
      rcases h5 with h5 | h5
      · exact pr 0 2 (by omega) ⟨h4, h5⟩
      · exact pf 1 1 (by omega) ⟨h4, h5⟩


theorem bound_of_none (k : ℕ) (hk : 0 < k) (c : ℝ)
    (h : ∀ w : ℕ → Fin k, ¬ UndirectedFree c w) : c ≤ URT k := by
  have hne : ({r : ℝ | Avoidable k r}).Nonempty :=
    ⟨3, ⟨fun _ => ⟨0, hk⟩, fun i n s hs => no_big_power s hs _⟩⟩
  refine le_csInf hne ?_
  rintro r ⟨w, hw⟩
  by_contra hlt
  push_neg at hlt
  exact h w (fun i n s hs => hw i n s (le_of_lt (lt_of_lt_of_le hlt hs)))

theorem lower_bound_all (k : ℕ) (hk : 4 ≤ k) : ((k : ℝ) - 1) / ((k : ℝ) - 2) ≤ URT k := by
  match k, hk with
  | 4, _ => exact bound_of_none 4 (by norm_num) _ (fun w hw => thm4 w (by norm_num at hw ⊢; exact hw))
  | 5, _ => exact bound_of_none 5 (by norm_num) _ (fun w hw => thm5 w (by norm_num at hw ⊢; exact hw))
  | (q + 6), _ =>
      exact bound_of_none (q + 6) (by omega) _ (fun w hw => thm3 q w (by push_cast at hw ⊢; exact hw))


theorem proof : statement := lower_bound_all

end Submissions.UndirectedLowerBoundAllK.OpusFamilySweep
