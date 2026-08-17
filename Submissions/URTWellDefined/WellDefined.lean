import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
Proof of `Statements.URTWellDefined.statement`.

The five definitions are re-declared verbatim (a submission may not import `Statements.*`);
the anti-restatement bridge checks them for definitional equality against the canonical file.
-/

namespace Submissions.URTWellDefined.WellDefined



variable {α : Type*}

/-- An **undirected `r`-power**: a word `xyx′` with `x` nonempty, `x′ ∈ {x, xᴿ}`, and
`|xyx′|/|xy| = r`. Currie–Mol Section 1, verbatim. The ratio is written as the multiplication
`|xyx′| = r * |xy|` to avoid a division; `|xy| ≥ 1` because `x` is nonempty. -/
def IsUndirectedPower (r : ℝ) (z : List α) : Prop :=
  ∃ x y x' : List α,
    z = x ++ y ++ x' ∧ x ≠ [] ∧ (x' = x ∨ x' = x.reverse) ∧
      (z.length : ℝ) = r * ((x ++ y).length : ℝ)

/-- The length-`n` factor of the infinite word `w` beginning at position `i`. -/
def factor (w : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => w (i + j)

/-- `w` is **undirected `r`-free**: no factor of `w` is an undirected `s`-power for any
`s ≥ r`. Currie–Mol Section 1: "`α`-free up to `∼` if no factor of `w` is an `r`-power up to
`∼` for `r ≥ α`". -/
def UndirectedFree (r : ℝ) (w : ℕ → α) : Prop :=
  ∀ (i n : ℕ) (s : ℝ), r ≤ s → ¬ IsUndirectedPower s (factor w i n)

/-- Undirected `r`-powers are **`k`-avoidable**: some infinite word on `k` letters is
undirected `r`-free. -/
def Avoidable (k : ℕ) (r : ℝ) : Prop := ∃ w : ℕ → Fin k, UndirectedFree r w

/-- The **undirected repetition threshold** `URT(k) = inf {r : undirected r-powers are
k-avoidable}`. -/
noncomputable def URT (k : ℕ) : ℝ := sInf {r : ℝ | Avoidable k r}
/-! ## 1. Non-vacuity witnesses for `IsUndirectedPower`. -/

/-- `aa` is an undirected 2-power (`x = [0]`, `y = []`, `x' = x`). -/
theorem witness_square : IsUndirectedPower (2 : ℝ) ([0, 0] : List (Fin 4)) :=
  ⟨[0], [], [0], by simp, by simp, Or.inl rfl, by norm_num⟩

/-- `abba` is an undirected 2-power via the *reversal* branch (`x = [0,1]`, `x' = xᴿ`). -/
theorem witness_reverse : IsUndirectedPower (2 : ℝ) ([0, 1, 1, 0] : List (Fin 4)) :=
  ⟨[0, 1], [], [1, 0], by simp, by simp, Or.inr (by decide), by norm_num⟩

/-- `aba` is an undirected `3/2`-power. -/
theorem witness_three_halves : IsUndirectedPower (3 / 2 : ℝ) ([0, 1, 0] : List (Fin 4)) :=
  ⟨[0], [1], [0], by simp, by simp, Or.inl rfl, by norm_num⟩

/-- And such a word really occurs as a `factor` of an infinite word. -/
theorem witness_factor : IsUndirectedPower (2 : ℝ) (factor (fun _ => (0 : Fin 4)) 7 2) :=
  ⟨[0], [], [0], by simp [factor], by simp, Or.inl rfl, by norm_num [factor]⟩


/-! ## 2. Every `r > 2` is avoidable: the defining set is NONEMPTY (so `sInf` is not junk-∅). -/

theorem len_eq {α : Type*} {x x' : List α} (h : x' = x ∨ x' = x.reverse) :
    x'.length = x.length := by
  rcases h with rfl | rfl
  · rfl
  · simp

theorem free_of_two_lt {α : Type*} (r : ℝ) (hr : 2 < r) (w : ℕ → α) : UndirectedFree r w := by
  rintro i n s hrs ⟨x, y, x', hz, hx, hx', hlen⟩
  have hxl : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hz' : (factor w i n).length = x.length + y.length + x'.length := by
    rw [hz]; simp [List.length_append, Nat.add_assoc]
  rw [hz', len_eq hx'] at hlen
  simp only [List.length_append] at hlen
  push_cast at hlen
  have h1 : (1:ℝ) ≤ (x.length : ℝ) := by exact_mod_cast hxl
  have h2 : (0:ℝ) ≤ (y.length : ℝ) := by positivity
  nlinarith [hlen]

theorem avoidable_of_two_lt (k : ℕ) (hk : 0 < k) (r : ℝ) (hr : 2 < r) : Avoidable k r :=
  ⟨fun _ => ⟨0, hk⟩, free_of_two_lt r hr _⟩

/-! ## 3. No `r ≤ 1` is avoidable: the defining set is BOUNDED BELOW by 1. -/

theorem factor_cons {α : Type*} (w : ℕ → α) (i n : ℕ) :
    factor w i (n + 1) = w i :: factor w (i + 1) n := by
  simp [factor, List.range_succ_eq_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

theorem factor_snoc {α : Type*} (w : ℕ → α) (i n : ℕ) :
    factor w i (n + 1) = factor w i n ++ [w (i + n)] := by
  simp [factor, List.range_succ]

theorem factor_split {α : Type*} (w : ℕ → α) (i e : ℕ) :
    factor w i (e + 2) = [w i] ++ factor w (i + 1) e ++ [w (i + 1 + e)] := by
  rw [factor_cons, factor_snoc]
  simp

theorem not_avoidable_of_le_one (k : ℕ) (r : ℝ) (hr : r ≤ 1) : ¬ Avoidable k r := by
  rintro ⟨w, hw⟩
  obtain ⟨a, b, hab, hval⟩ := Finite.exists_ne_map_eq_of_infinite w
  obtain ⟨i, j, hij, hv⟩ : ∃ i j : ℕ, i < j ∧ w i = w j := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, hval⟩
    · exact ⟨b, a, h, hval.symm⟩
  obtain ⟨e, he⟩ : ∃ e, j = i + 1 + e := ⟨j - i - 1, by omega⟩
  have hpos : (0:ℝ) < (e : ℝ) + 1 := by positivity
  have hs1 : (1:ℝ) < ((e : ℝ) + 2) / ((e : ℝ) + 1) := by
    rw [lt_div_iff₀ hpos]; linarith
  refine hw i (e + 2) (((e : ℝ) + 2) / ((e : ℝ) + 1)) (hr.trans hs1.le) ?_
  refine ⟨[w i], factor w (i + 1) e, [w j], ?_, by simp, Or.inl ?_, ?_⟩
  · rw [factor_split, he]
  · rw [hv, he]
  · rw [factor_split]
    simp only [List.length_append, List.length_cons, List.length_nil, factor,
      List.length_map, List.length_range]
    push_cast
    field_simp
    ring


/-! ## 4. The bracket, with the upper end at 2 rather than 3. -/

theorem urt_bracket (k : ℕ) (hk : 0 < k) : 1 ≤ URT k ∧ URT k ≤ 2 := by
  have hbdd : ∀ r ∈ {r : ℝ | Avoidable k r}, (1:ℝ) ≤ r := by
    intro r hrm
    by_contra hlt
    exact not_avoidable_of_le_one k r (le_of_lt (not_le.mp hlt)) hrm
  have hne : (3:ℝ) ∈ {r : ℝ | Avoidable k r} := avoidable_of_two_lt k hk 3 (by norm_num)
  refine ⟨le_csInf ⟨3, hne⟩ hbdd, ?_⟩
  refine le_of_forall_pos_le_add ?_
  intro e he
  exact csInf_le ⟨1, fun r hr => hbdd r hr⟩ (avoidable_of_two_lt k hk (2 + e) (by linarith))

theorem proof :
    IsUndirectedPower (2 : ℝ) ([0, 0] : List (Fin 4)) ∧
    IsUndirectedPower (2 : ℝ) ([0, 1, 1, 0] : List (Fin 4)) ∧
    (∀ k : ℕ, 0 < k → 1 ≤ URT k ∧ URT k ≤ 2) :=
  ⟨witness_square, witness_reverse, urt_bracket⟩

end Submissions.URTWellDefined.WellDefined
