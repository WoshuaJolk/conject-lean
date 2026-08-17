import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Commons.SetPairSystem

/-!
Route, in two independent halves.

* `unit_le_two` : `m(1,1,1) ≤ 2`.  With `|A i| ≤ 1` the cross clause `(A i ∩ B j).card = 1`
  pins `A i` and `B j` to the SAME singleton for every `i ≠ j`.  Three distinct indices then
  force `A i₀ = B i₀`, which collides with the disjointness clause `A i₀ ∩ B i₀ = ∅` because
  the common value is nonempty.  No decidability, no enumeration; `m` is arbitrary.

* `pentagon` : `m(2,2,1) ≥ 5`.  The explicit rotational system on the ground set `{0,1,2,3,4}`,
  `A i = {i, i+1}` and `B i = {i+2, i+4}` (indices mod 5), checked by `decide`.

`5 > 4 = 2 * 2` is then the failure of submultiplicativity at the split `(1,1) + (1,1)`.
-/

namespace Submissions.SubmultiplicativityFails.PentagonUnitCase

/-- `A i = {i, i+1}` on `ℤ/5`, written out. -/
def Apent : Fin 5 → Finset ℕ :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}]

/-- `B i = {i+2, i+4}` on `ℤ/5`, written out. -/
def Bpent : Fin 5 → Finset ℕ :=
  ![{2, 4}, {3, 0}, {4, 1}, {0, 2}, {1, 3}]

theorem pentagon : Commons.OneCrossSPS 2 2 5 Apent Bpent := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- With `|A i| ≤ 1` and `|B j| ≤ 1`, the cross clause forces `A i = B j` for `i ≠ j`. -/
theorem unit_le_two (m : ℕ) (A B : Fin m → Finset ℕ)
    (h : Commons.OneCrossSPS 1 1 m A B) : m ≤ 2 := by
  obtain ⟨hA, hB, hdisj, hcross⟩ := h
  -- for `i ≠ j`, both `A i` and `B j` are the singleton `{x}` cutting them out
  have key : ∀ i j : Fin m, i ≠ j → A i = B j ∧ (A i).Nonempty := by
    intro i j hij
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 (hcross i j hij)
    have hmem : x ∈ A i ∩ B j := by rw [hx]; exact Finset.mem_singleton_self x
    have hxA : x ∈ A i := (Finset.mem_inter.1 hmem).1
    have hxB : x ∈ B j := (Finset.mem_inter.1 hmem).2
    have h1 : A i = {x} :=
      Finset.eq_singleton_iff_unique_mem.2
        ⟨hxA, fun y hy => Finset.card_le_one.1 (hA i) y hy x hxA⟩
    have h2 : B j = {x} :=
      Finset.eq_singleton_iff_unique_mem.2
        ⟨hxB, fun y hy => Finset.card_le_one.1 (hB j) y hy x hxB⟩
    exact ⟨by rw [h1, h2], ⟨x, hxA⟩⟩
  by_contra hmle
  have hm : 2 < m := Nat.not_le.1 hmle
  -- three distinct indices exist
  have h0 : (0 : ℕ) < m := by omega
  have h1' : (1 : ℕ) < m := by omega
  have h2' : (2 : ℕ) < m := by omega
  set i0 : Fin m := ⟨0, h0⟩ with hi0
  set i1 : Fin m := ⟨1, h1'⟩ with hi1
  set i2 : Fin m := ⟨2, h2'⟩ with hi2
  have n01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have n10 : i1 ≠ i0 := by simp [hi0, hi1, Fin.ext_iff]
  have n02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have n12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  obtain ⟨e01, hne0⟩ := key i0 i1 n01
  obtain ⟨e02, -⟩ := key i0 i2 n02
  obtain ⟨e12, -⟩ := key i1 i2 n12
  obtain ⟨e10, -⟩ := key i1 i0 n10
  -- `A i0 = B i2 = A i1 = B i0`
  have hAA : A i0 = A i1 := by rw [e02, ← e12]
  have hcollide : A i0 = B i0 := by rw [hAA, e10]
  have : A i0 = (∅ : Finset ℕ) := by
    have := hdisj i0
    rwa [← hcollide, Finset.inter_self] at this
  exact absurd this (Finset.nonempty_iff_ne_empty.1 hne0)

/-- The canonical proposition of `Statements.SubmultiplicativityFails`. -/
theorem proof :
    (∀ (m : ℕ) (A B : Fin m → Finset ℕ), Commons.OneCrossSPS 1 1 m A B → m ≤ 2) ∧
    (∃ A B : Fin 5 → Finset ℕ, Commons.OneCrossSPS 2 2 5 A B) :=
  ⟨unit_le_two, ⟨Apent, Bpent, pentagon⟩⟩

end Submissions.SubmultiplicativityFails.PentagonUnitCase
