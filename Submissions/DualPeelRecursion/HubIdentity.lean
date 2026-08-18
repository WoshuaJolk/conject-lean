import Mathlib
import Commons.SetPairSystem

/-!
Proof of `Statements.DualPeelRecursion.statement`: an `(a, b+1)`-bounded 1-cross
intersecting set pair system of size `m` contains an `(a, b)`-bounded one of size `m'`
with `m ≤ a * m' + 1`.  Take the largest fibre `T e`, `e ∈ A i`; the fibre-count identity
bounds `m - 1` by `a * |T e|`, and deleting `e` from every `B j` on that fibre lowers the
`b`-budget by one without disturbing any cross condition.
-/

namespace Submissions.DualPeelRecursion.HubIdentity


open Finset

/-- `Tset B e` is the set of indices `j` with `e ∈ B j`. -/
def Tset {m : ℕ} (B : Fin m → Finset ℕ) (e : ℕ) : Finset (Fin m) :=
  univ.filter (fun j => e ∈ B j)

lemma card_Tset {m : ℕ} (B : Fin m → Finset ℕ) (e : ℕ) :
    (Tset B e).card = ∑ j : Fin m, (if e ∈ B j then 1 else 0) := by
  rw [Tset, Finset.card_filter]

/-- The fibre-count identity. -/
theorem fibre_identity {a b m : ℕ} {A B : Fin m → Finset ℕ}
    (h : Commons.OneCrossSPS a b m A B) (i : Fin m) :
    (∑ e ∈ A i, (Tset B e).card) + 1 = m := by
  obtain ⟨-, -, hdisj, hcross⟩ := h
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have key : ∀ j : Fin m, (∑ e ∈ A i, (if e ∈ B j then 1 else 0)) = (A i ∩ B j).card := by
    intro j
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  have step : (∑ e ∈ A i, (Tset B e).card) = ∑ j : Fin m, (A i ∩ B j).card := by
    simp_rw [card_Tset]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => key j)
  have h0 : (A i ∩ B i).card = 0 := by rw [hdisj i]; simp
  have h1 : ∀ j ∈ univ.erase i, (A i ∩ B j).card = 1 := by
    intro j hj
    exact hcross i j (Ne.symm (Finset.ne_of_mem_erase hj))
  have hsplit : (∑ j : Fin m, (A i ∩ B j).card)
      = (A i ∩ B i).card + ∑ j ∈ univ.erase i, (A i ∩ B j).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have herase : (univ.erase i).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [step, hsplit, h0, Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one, herase]
  omega

/-- Ground-degree ceiling: if every ground element lies in at most `t` of the `B j`, then
`m ≤ a * t + 1`. -/
theorem degree_ceiling {a b m t : ℕ} {A B : Fin m → Finset ℕ}
    (h : Commons.OneCrossSPS a b m A B)
    (hdeg : ∀ e : ℕ, (Tset B e).card ≤ t) : m ≤ a * t + 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · omega
  · set i : Fin m := ⟨0, hm⟩ with hi
    have hid := fibre_identity h i
    have hcard : (A i).card ≤ a := h.1 i
    have hb1 : (∑ e ∈ A i, (Tset B e).card) ≤ (A i).card * t := by
      calc (∑ e ∈ A i, (Tset B e).card) ≤ ∑ _e ∈ A i, t :=
            Finset.sum_le_sum (fun e _ => hdeg e)
        _ = (A i).card * t := by rw [Finset.sum_const, smul_eq_mul]
    have hb2 : (∑ e ∈ A i, (Tset B e).card) ≤ a * t :=
      le_trans hb1 (Nat.mul_le_mul_right t hcard)
    omega

/-- Restriction: for any ground element `e`, the subsystem indexed by `Tset B e`, with
`B` shrunk by deleting `e`, is an `(a, b)`-bounded 1-cross intersecting SPS. -/
theorem restrict_T {a b m : ℕ} {A B : Fin m → Finset ℕ}
    (h : Commons.OneCrossSPS a (b + 1) m A B) (e : ℕ) :
    ∃ A' B' : Fin (Tset B e).card → Finset ℕ,
      Commons.OneCrossSPS a b (Tset B e).card A' B' := by
  classical
  refine ⟨fun k => A (((Tset B e).equivFin.symm k : Fin m)),
          fun k => (B (((Tset B e).equivFin.symm k : Fin m))).erase e, ?_, ?_, ?_, ?_⟩
  · intro k; exact h.1 _
  · intro k
    have hmem : e ∈ B (((Tset B e).equivFin.symm k : Fin m)) := by
      have h2 := ((Tset B e).equivFin.symm k).2
      simp only [Tset, Finset.mem_filter] at h2
      exact h2.2
    have h1 : (B (((Tset B e).equivFin.symm k : Fin m))).card ≤ b + 1 := h.2.1 _
    rw [Finset.card_erase_of_mem hmem]
    omega
  · intro k
    have hsub : A (((Tset B e).equivFin.symm k : Fin m))
        ∩ (B (((Tset B e).equivFin.symm k : Fin m))).erase e
        ⊆ A (((Tset B e).equivFin.symm k : Fin m))
        ∩ B (((Tset B e).equivFin.symm k : Fin m)) :=
      Finset.inter_subset_inter (subset_refl _) (Finset.erase_subset _ _)
    rw [h.2.2.1 _] at hsub
    exact Finset.subset_empty.mp hsub
  · intro k k' hkk'
    have hinj : Function.Injective
        (fun k : Fin (Tset B e).card => (((Tset B e).equivFin.symm k : Fin m))) := by
      intro x y hxy
      exact (Tset B e).equivFin.symm.injective (Subtype.ext hxy)
    have hne : (((Tset B e).equivFin.symm k : Fin m))
        ≠ (((Tset B e).equivFin.symm k' : Fin m)) := fun hc => hkk' (hinj hc)
    have hcross := h.2.2.2 _ _ hne
    have hmemk : e ∈ B (((Tset B e).equivFin.symm k : Fin m)) := by
      have h2 := ((Tset B e).equivFin.symm k).2
      simp only [Tset, Finset.mem_filter] at h2
      exact h2.2
    have henotA : e ∉ A (((Tset B e).equivFin.symm k : Fin m)) := by
      intro hc
      have hmem : e ∈ A (((Tset B e).equivFin.symm k : Fin m))
          ∩ B (((Tset B e).equivFin.symm k : Fin m)) := Finset.mem_inter.2 ⟨hc, hmemk⟩
      rw [h.2.2.1 _] at hmem
      simp at hmem
    have heq : A (((Tset B e).equivFin.symm k : Fin m))
        ∩ (B (((Tset B e).equivFin.symm k' : Fin m))).erase e
        = A (((Tset B e).equivFin.symm k : Fin m))
        ∩ B (((Tset B e).equivFin.symm k' : Fin m)) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hx1, -, hx3⟩; exact ⟨hx1, hx3⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx1, by rintro rfl; exact henotA hx1, hx2⟩
    rw [heq]; exact hcross

/-- Dual peel: an `(a, b+1)`-bounded system of size `m` yields an `(a, b)`-bounded one of
size `m'` with `m ≤ a * m' + 1`. -/
theorem dual_peel {a b m : ℕ} {A B : Fin m → Finset ℕ}
    (h : Commons.OneCrossSPS a (b + 1) m A B) :
    ∃ (m' : ℕ) (A' B' : Fin m' → Finset ℕ),
      Commons.OneCrossSPS a b m' A' B' ∧ m ≤ a * m' + 1 := by
  classical
  have triv : ∀ (A' B' : Fin 0 → Finset ℕ), Commons.OneCrossSPS a b 0 A' B' := by
    intro A' B'
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact ⟨0, (fun _ => ∅), (fun _ => ∅), triv _ _, by omega⟩
  have hid := fibre_identity h (⟨0, hm⟩ : Fin m)
  rcases Finset.eq_empty_or_nonempty (A (⟨0, hm⟩ : Fin m)) with hAi | hAi
  · refine ⟨0, (fun _ => ∅), (fun _ => ∅), triv _ _, ?_⟩
    rw [hAi] at hid; simp at hid; omega
  obtain ⟨e, he, hemax⟩ :=
    Finset.exists_max_image (A (⟨0, hm⟩ : Fin m)) (fun e => (Tset B e).card) hAi
  have hb1 : (∑ f ∈ A (⟨0, hm⟩ : Fin m), (Tset B f).card)
      ≤ (A (⟨0, hm⟩ : Fin m)).card * (Tset B e).card :=
    calc (∑ f ∈ A (⟨0, hm⟩ : Fin m), (Tset B f).card)
        ≤ ∑ _f ∈ A (⟨0, hm⟩ : Fin m), (Tset B e).card :=
          Finset.sum_le_sum (fun f hf => hemax f hf)
      _ = (A (⟨0, hm⟩ : Fin m)).card * (Tset B e).card := by
          rw [Finset.sum_const, smul_eq_mul]
  have hb2 : (∑ f ∈ A (⟨0, hm⟩ : Fin m), (Tset B f).card) ≤ a * (Tset B e).card :=
    le_trans hb1 (Nat.mul_le_mul_right _ (h.1 _))
  obtain ⟨A', B', hA'B'⟩ := restrict_T h e
  exact ⟨(Tset B e).card, A', B', hA'B', by omega⟩


/-- The submitted declaration. -/
theorem proof : ∀ (a b m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS a (b + 1) m A B →
      ∃ (m' : ℕ) (A' B' : Fin m' → Finset ℕ),
        Commons.OneCrossSPS a b m' A' B' ∧ m ≤ a * m' + 1 :=
  fun _ _ _ _ _ h => dual_peel h

end Submissions.DualPeelRecursion.HubIdentity
