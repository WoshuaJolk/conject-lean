import Mathlib

namespace Submissions.GenPosUPB344Dead.GenPosCount

abbrev GenPos3 (u : Fin 10 → Fin 3 → ℂ) : Prop :=
  ∀ i j k : Fin 10, i ≠ j → i ≠ k → j ≠ k → LinearIndependent ℂ ![u i, u j, u k]

abbrev GenPos4 (x : Fin 10 → Fin 4 → ℂ) : Prop :=
  ∀ i j k l : Fin 10, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    LinearIndependent ℂ ![x i, x j, x k, x l]

def ip {d : ℕ} (x y : Fin d → ℂ) : ℂ :=
  ∑ r, star (x r) * y r

lemma full_kills {d : ℕ} [NeZero d] (v : Fin d → Fin d → ℂ) (y : Fin d → ℂ)
    (hv : LinearIndependent ℂ v) (h : ∀ t, ip y (v t) = 0) : y = 0 := by
  let L : (Fin d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => ip y x
      map_add' := by
        intro x z
        simp [ip, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c x
        change (∑ r, star (y r) * (c * x r)) = c * ∑ r, star (y r) * x r
        calc
          _ = ∑ r, c * (star (y r) * x r) := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ = _ := by rw [Finset.mul_sum] }
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank (by
      simp [Module.finrank_fintype_fun_eq_card])
  have hsub : Submodule.span ℂ (Set.range v) ≤ LinearMap.ker L :=
    Submodule.span_le.2 (by
      rintro _ ⟨t, rfl⟩
      exact (LinearMap.mem_ker).2 (h t))
  have hyker : y ∈ LinearMap.ker L := by
    apply hsub
    rw [hspan]
    exact Submodule.mem_top
  have hLy : L y = 0 := (LinearMap.mem_ker).1 hyker
  have hinner :
      inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 y) = 0 := by
    calc
      inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 y) =
          ∑ r, star (y r) * y r := by
            rw [PiLp.inner_apply]
            apply Finset.sum_congr rfl
            intro r hr
            rw [RCLike.inner_apply]
            simp only [starRingEnd_apply]
            ring
      _ = L y := by rfl
      _ = 0 := hLy
  have hto : WithLp.toLp 2 y = 0 :=
    (inner_self_eq_zero (𝕜 := ℂ)).1 hinner
  exact (WithLp.toLp_eq_zero 2).1 hto

theorem proof :
    ¬ ∃ u : Fin 10 → Fin 3 → ℂ,
      ∃ w : Fin 10 → Fin 4 → ℂ,
      ∃ z : Fin 10 → Fin 4 → ℂ,
        (∀ i, u i ≠ 0) ∧
        (∀ i, w i ≠ 0) ∧
        (∀ i, z i ≠ 0) ∧
        (∀ i j, i ≠ j →
          (∑ r, star (u i r) * u j r) *
          (∑ r, star (w i r) * w j r) *
          (∑ r, star (z i r) * z j r) = 0) ∧
        GenPos3 u ∧ GenPos4 w ∧ GenPos4 z := by
  classical
  rintro ⟨u, w, z, hu0, hw0, hz0, horth, hgu, hgw, hgz⟩
  let S : Finset (Fin 10) := Finset.univ.erase (0 : Fin 10)
  let A : Finset (Fin 10) :=
    S.filter (fun j => ip (u 0) (u j) = 0)
  let B : Finset (Fin 10) :=
    S.filter (fun j => ip (w 0) (w j) = 0)
  let C : Finset (Fin 10) :=
    S.filter (fun j => ip (z 0) (z j) = 0)
  have hcover : S ⊆ A ∪ B ∪ C := by
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    have h := horth 0 j (Ne.symm hj0)
    rcases mul_eq_zero.mp h with hAB | hC
    · rcases mul_eq_zero.mp hAB with hA | hB
      · exact Finset.mem_union_left C
          (Finset.mem_union_left B
            (Finset.mem_filter.mpr ⟨hj, by simpa [ip] using hA⟩))
      · exact Finset.mem_union_left C
          (Finset.mem_union_right A
            (Finset.mem_filter.mpr ⟨hj, by simpa [ip] using hB⟩))
    · exact Finset.mem_union_right (A ∪ B)
        (Finset.mem_filter.mpr ⟨hj, by simpa [ip] using hC⟩)
  have hcard_lower : 9 ≤ A.card + B.card + C.card := by
    have hS : S.card = 9 := by simp [S]
    have h₁ : 9 ≤ (A ∪ B ∪ C).card := by
      rw [← hS]
      exact Finset.card_le_card hcover
    have h₂ : (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by
      calc
        (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
        _ ≤ (A.card + B.card) + C.card := by
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ = A.card + B.card + C.card := by omega
    omega
  have hAcard : A.card ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ A.card := by omega
    obtain ⟨t, htA, ht⟩ := Finset.exists_subset_card_eq (s := A) (n := 3) hthree
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp ht
    have hi := (Finset.mem_filter.mp
      (htA (by simp : i ∈ ({i, j, k} : Finset (Fin 10))))).2
    have hj := (Finset.mem_filter.mp
      (htA (by simp : j ∈ ({i, j, k} : Finset (Fin 10))))).2
    have hk := (Finset.mem_filter.mp
      (htA (by simp : k ∈ ({i, j, k} : Finset (Fin 10))))).2
    have hzero : u 0 = 0 := full_kills ![u i, u j, u k] (u 0)
      (hgu i j k hij hik hjk) (by
        intro t
        fin_cases t
        · simpa using hi
        · simpa using hj
        · simpa using hk)
    exact (hu0 0) hzero
  have hBcard : B.card ≤ 3 := by
    by_contra hnot
    have hfour : 4 ≤ B.card := by omega
    obtain ⟨t, htB, ht⟩ := Finset.exists_subset_card_eq (s := B) (n := 4) hfour
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ :=
      Finset.card_eq_four.mp ht
    have hi := (Finset.mem_filter.mp
      (htB (by simp : i ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hj := (Finset.mem_filter.mp
      (htB (by simp : j ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hk := (Finset.mem_filter.mp
      (htB (by simp : k ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hl := (Finset.mem_filter.mp
      (htB (by simp : l ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hzero : w 0 = 0 := full_kills ![w i, w j, w k, w l] (w 0)
      (hgw i j k l hij hik hil hjk hjl hkl) (by
        intro t
        fin_cases t
        · simpa using hi
        · simpa using hj
        · simpa using hk
        · simpa using hl)
    exact (hw0 0) hzero
  have hCcard : C.card ≤ 3 := by
    by_contra hnot
    have hfour : 4 ≤ C.card := by omega
    obtain ⟨t, htC, ht⟩ := Finset.exists_subset_card_eq (s := C) (n := 4) hfour
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ :=
      Finset.card_eq_four.mp ht
    have hi := (Finset.mem_filter.mp
      (htC (by simp : i ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hj := (Finset.mem_filter.mp
      (htC (by simp : j ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hk := (Finset.mem_filter.mp
      (htC (by simp : k ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hl := (Finset.mem_filter.mp
      (htC (by simp : l ∈ ({i, j, k, l} : Finset (Fin 10))))).2
    have hzero : z 0 = 0 := full_kills ![z i, z j, z k, z l] (z 0)
      (hgz i j k l hij hik hil hjk hjl hkl) (by
        intro t
        fin_cases t
        · simpa using hi
        · simpa using hj
        · simpa using hk
        · simpa using hl)
    exact (hz0 0) hzero
  omega

end Submissions.GenPosUPB344Dead.GenPosCount
