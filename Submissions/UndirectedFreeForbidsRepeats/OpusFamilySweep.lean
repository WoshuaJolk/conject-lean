import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
Clause 1 is one application of `UndirectedFree` to the explicit three-block decomposition
`factor w i (2l+m) = factor w i l ++ factor w (i+l) m ++ factor w (i+l+m) l`, at the exponent
`s = (2l+m)/(l+m)`. Clause 2 instantiates it at `l = 1, r = (d+1)/d` and at `l = 2,
r = (m+4)/(m+2)`, in each case checking `(k-1)/(k-2) < r` from the integer side condition.

Controls run against these definitions before submitting: the conclusion of clause 2 is
provably FALSE for the constant word over `Fin 4` (both sub-clauses), so neither is a
tautology and the plus-freeness hypothesis is load-bearing.
-/

namespace Submissions.UndirectedFreeForbidsRepeats.OpusFamilySweep
variable {α : Type*}

def IsUndirectedPower (r : ℝ) (z : List α) : Prop :=
  ∃ x y x' : List α,
    z = x ++ y ++ x' ∧ x ≠ [] ∧ (x' = x ∨ x' = x.reverse) ∧
      (z.length : ℝ) = r * ((x ++ y).length : ℝ)

def factor (w : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => w (i + j)

def UndirectedFree (r : ℝ) (w : ℕ → α) : Prop :=
  ∀ (i n : ℕ) (s : ℝ), r ≤ s → ¬ IsUndirectedPower s (factor w i n)

abbrev statement : Prop :=
  ∀ (k : ℕ) (w : ℕ → Fin k),
    (∀ (r : ℝ), UndirectedFree r w →
        ∀ i l m : ℕ, 1 ≤ l → r * ((l : ℝ) + (m : ℝ)) ≤ 2 * (l : ℝ) + (m : ℝ) →
          factor w (i + l + m) l ≠ factor w i l ∧
          factor w (i + l + m) l ≠ (factor w i l).reverse)
    ∧ (4 ≤ k → (∀ r : ℝ, ((k : ℝ) - 1) / ((k : ℝ) - 2) < r → UndirectedFree r w) →
        (∀ i d : ℕ, 1 ≤ d → d + 3 ≤ k → w i ≠ w (i + d)) ∧
        (∀ i m : ℕ, m + 7 ≤ 2 * k →
          ¬ (w (i + 2 + m) = w i ∧ w (i + 3 + m) = w (i + 1)) ∧
          ¬ (w (i + 2 + m) = w (i + 1) ∧ w (i + 3 + m) = w i)))

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
      push_cast
      field_simp
  exact ⟨fun h => main (Or.inl h), fun h => main (Or.inr h)⟩

theorem proof : statement := by
  intro k w
  refine ⟨fun r hf i l m hl hexp => gen w r hf i l m hl hexp, ?_⟩
  intro hk hplus
  have hk2 : (0:ℝ) < (k:ℝ) - 2 := by
    have : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  constructor
  · rintro i d hd hdk
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    set r : ℝ := ((e:ℝ) + 2) / ((e:ℝ) + 1) with hrdef
    have he1 : (0:ℝ) < (e:ℝ) + 1 := by positivity
    have hlt : ((k : ℝ) - 1) / ((k : ℝ) - 2) < r := by
      rw [hrdef, div_lt_div_iff₀ hk2 he1]
      have : ((e:ℝ) + 1) + 3 ≤ (k:ℝ) := by exact_mod_cast hdk
      nlinarith
    have := (gen w r (hplus r hlt) i 1 e le_rfl (by
      rw [hrdef]; push_cast; rw [div_mul_eq_mul_div, div_le_iff₀ (by push_cast at he1 ⊢; linarith)]
      ring_nf; nlinarith [he1])).1
    intro hc
    apply this
    have hi : i + 1 + e = i + (e + 1) := by omega
    rw [hi, factor_one, factor_one, hc]
  · rintro i m hm
    set r : ℝ := ((m:ℝ) + 4) / ((m:ℝ) + 2) with hrdef
    have hm2 : (0:ℝ) < (m:ℝ) + 2 := by positivity
    have hlt : ((k : ℝ) - 1) / ((k : ℝ) - 2) < r := by
      rw [hrdef, div_lt_div_iff₀ hk2 hm2]
      have : (m:ℝ) + 7 ≤ 2 * (k:ℝ) := by exact_mod_cast hm
      nlinarith
    have hg := gen w r (hplus r hlt) i 2 m (by omega) (by
      rw [hrdef]; push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      ring_nf; nlinarith)
    have hi : i + 2 + m + 1 = i + 3 + m := by omega
    constructor
    · rintro ⟨h1, h2⟩
      exact hg.1 (by rw [factor_two, factor_two, hi, h1, h2])
    · rintro ⟨h1, h2⟩
      exact hg.2 (by rw [factor_two, factor_two, hi, h1, h2]; simp)

end Submissions.UndirectedFreeForbidsRepeats.OpusFamilySweep
