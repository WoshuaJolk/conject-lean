import Mathlib

namespace Submissions.CopiesTransversalCore.Core

variable {k : ℕ}

abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

abbrev Tight {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card ≤ k - 1 → LinearIndependent ℂ fun i : (S : Set ι) => v i

abbrev Spanning {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i) = ⊤

abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) : Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

theorem target : ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      Tight u → Spanning u → Tight w → Spanning w →
      (∀ (i : Fin n₁) (j : Fin n₂), pair (u i) (w j) ≠ 0) →
      Transversal u w →
      Tight (Sum.elim u w) ∧ Spanning (Sum.elim u w) ∧
        (∀ a b : Fin n₁ ⊕ Fin n₂,
          pair (Sum.elim u w a) (Sum.elim u w b) = 0 →
              (∃ i j, a = Sum.inl i ∧ b = Sum.inl j) ∨
              (∃ i j, a = Sum.inr i ∧ b = Sum.inr j)) := by
  intro k n₁ n₂ hk u w htu hsu htw hsw hcross htrans
  have li_iff_rk_eq_card :
      ∀ {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) (S : Finset ι),
        (LinearIndependent ℂ (fun i : (S : Set ι) => v i) ↔
          rk v S = S.card) := by
    intro ι _ v S
    change LinearIndependent ℂ (fun i : (S : Set ι) => v i) ↔
      Module.finrank ℂ
        (Submodule.span ℂ (Set.range (fun i : (S : Set ι) => v i))) = S.card
    rw [linearIndependent_iff_card_eq_finrank_span]
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    change S.card = Module.finrank ℂ
      (Submodule.span ℂ (Set.range (fun i : (S : Set ι) => v i))) ↔ _
    exact eq_comm
  have rk_mono :
      ∀ {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) {S T : Finset ι},
        S ⊆ T → rk v S ≤ rk v T := by
    intro ι _ v S T hST
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, hST i.property⟩, rfl⟩
  have rank_top (v : Fin n₁ → Fin k → ℂ) (S : Finset (Fin n₁))
      (h : Submodule.span ℂ (Set.range (fun i : (S : Set (Fin n₁)) => v i)) = ⊤) :
      rk v S = k := by
    unfold rk
    rw [h]
    simp [Module.finrank_fintype_fun_eq_card]
  have rank_top' (v : Fin n₂ → Fin k → ℂ) (S : Finset (Fin n₂))
      (h : Submodule.span ℂ (Set.range (fun i : (S : Set (Fin n₂)) => v i)) = ⊤) :
      rk v S = k := by
    unfold rk
    rw [h]
    simp [Module.finrank_fintype_fun_eq_card]
  have hsingle_u (i : Fin n₁) : rk u {i} = 1 := by
    have h := (li_iff_rk_eq_card u {i}).1 (htu {i} (by
      simpa only [Finset.card_singleton] using (show 1 ≤ k - 1 by omega)))
    simpa using h
  have hsingle_w (i : Fin n₂) : rk w {i} = 1 := by
    have h := (li_iff_rk_eq_card w {i}).1 (htw {i} (by
      simpa only [Finset.card_singleton] using (show 1 ≤ k - 1 by omega)))
    simpa using h
  have hTight : Tight (Sum.elim u w) := by
    intro S hS
    let S₁ := S.toLeft
    let S₂ := S.toRight
    have hdecomp : S₁.disjSum S₂ = S := Finset.toLeft_disjSum_toRight
    have hcard : S₁.card + S₂.card = S.card := by
      rw [← Finset.card_disjSum S₁ S₂, hdecomp]
    have h₁ : S₁.card ≤ k - 1 := by omega
    have h₂ : S₂.card ≤ k - 1 := by omega
    have hu := (li_iff_rk_eq_card u S₁).1 (htu S₁ h₁)
    have hw := (li_iff_rk_eq_card w S₂).1 (htw S₂ h₂)
    have hrank : rk (Sum.elim u w) (S₁.disjSum S₂) = S.card := by
      calc
        rk (Sum.elim u w) (S₁.disjSum S₂) =
            min k (rk u S₁ + rk w S₂) := htrans S₁ S₂
        _ = min k (S₁.card + S₂.card) := by rw [hu, hw]
        _ = S.card := by rw [hcard, Nat.min_eq_right (by omega)]
    rw [← hdecomp]
    apply (li_iff_rk_eq_card (Sum.elim u w) (S₁.disjSum S₂)).2
    simpa [hdecomp] using hrank
  have hSpanning : Spanning (Sum.elim u w) := by
    intro S hS
    let S₁ := S.toLeft
    let S₂ := S.toRight
    have hdecomp : S₁.disjSum S₂ = S := Finset.toLeft_disjSum_toRight
    have hcard : S₁.card + S₂.card = S.card := by
      rw [← Finset.card_disjSum S₁ S₂, hdecomp]
    have hrank_sum : k ≤ rk u S₁ + rk w S₂ := by
      by_cases h₂empty : S₂ = ∅
      · have hc₁ : S₁.card = k + 1 := by
          have hz : S₂.card = 0 := Finset.card_eq_zero.mpr h₂empty
          omega
        have htop := hsu S₁ hc₁
        have hu : rk u S₁ = k := rank_top u S₁ htop
        simp [h₂empty, hu]
      · by_cases h₁empty : S₁ = ∅
        · have hc₂ : S₂.card = k + 1 := by
            have hz : S₁.card = 0 := Finset.card_eq_zero.mpr h₁empty
            omega
          have htop := hsw S₂ hc₂
          have hw : rk w S₂ = k := rank_top' w S₂ htop
          simp [h₁empty, hw]
        · have hc₁pos : 1 ≤ S₁.card := by
            exact Finset.one_le_card.2 (Finset.nonempty_iff_ne_empty.2 h₁empty)
          have hc₂pos : 1 ≤ S₂.card := by
            exact Finset.one_le_card.2 (Finset.nonempty_iff_ne_empty.2 h₂empty)
          have hc₁le : S₁.card ≤ k := by omega
          have hc₂le : S₂.card ≤ k := by omega
          by_cases hc₁eq : S₁.card = k
          · have hc₂one : S₂.card = 1 := by omega
            obtain ⟨j, hS₂eq⟩ := Finset.card_eq_one.mp hc₂one
            have hsub : ∃ R : Finset (Fin n₁), R ⊆ S₁ ∧ R.card = k - 1 :=
              Finset.exists_subset_card_eq (by omega)
            obtain ⟨R, hRsub, hRcard⟩ := hsub
            have hRrank : rk u R = k - 1 :=
              (li_iff_rk_eq_card u R).1 (htu R (by omega)) ▸ hRcard
            have hmono : rk u R ≤ rk u S₁ := rk_mono u hRsub
            have hw : rk w S₂ = 1 := by simpa [hS₂eq] using hsingle_w j
            omega
          · have hc₁le' : S₁.card ≤ k - 1 := by omega
            have hu : rk u S₁ = S₁.card :=
              (li_iff_rk_eq_card u S₁).1 (htu S₁ hc₁le')
            by_cases hc₂eq : S₂.card = k
            · have hc₁one : S₁.card = 1 := by omega
              obtain ⟨i, hS₁eq⟩ := Finset.card_eq_one.mp hc₁one
              have hw : rk w S₂ ≥ k - 1 := by
                have hsub : ∃ R : Finset (Fin n₂), R ⊆ S₂ ∧ R.card = k - 1 :=
                  Finset.exists_subset_card_eq (by omega)
                obtain ⟨R, hRsub, hRcard⟩ := hsub
                have hRrank : rk w R = k - 1 :=
                  (li_iff_rk_eq_card w R).1 (htw R (by omega)) ▸ hRcard
                exact hRrank ▸ rk_mono w hRsub
              have huone : rk u S₁ = 1 := by simpa [hS₁eq] using hsingle_u i
              omega
            · have hc₂le' : S₂.card ≤ k - 1 := by omega
              have hw : rk w S₂ = S₂.card :=
                (li_iff_rk_eq_card w S₂).1 (htw S₂ hc₂le')
              omega
    have hrank : rk (Sum.elim u w) (S₁.disjSum S₂) = k := by
      rw [htrans]
      rw [Nat.min_eq_left hrank_sum]
    have htop : Submodule.span ℂ
        (Set.range (fun i : ((S₁.disjSum S₂ : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
          Sum.elim u w i.1)) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa [rk, Module.finrank_fintype_fun_eq_card] using hrank
    rw [← hdecomp]
    exact htop
  have pair_symm (x y : Fin k → ℂ) : pair x y = star (pair y x) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp [pair, star_mul', mul_comm]
  have hOrth :
      ∀ a b : Fin n₁ ⊕ Fin n₂,
        pair (Sum.elim u w a) (Sum.elim u w b) = 0 →
          (∃ i j, a = Sum.inl i ∧ b = Sum.inl j) ∨
            (∃ i j, a = Sum.inr i ∧ b = Sum.inr j) := by
    intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j => exact Or.inl ⟨i, j, rfl, rfl⟩
        | inr j =>
            exfalso
            exact hcross i j (by simpa [pair] using hab)
    | inr i =>
        cases b with
        | inr j => exact Or.inr ⟨i, j, rfl, rfl⟩
        | inl j =>
            exfalso
            apply hcross j i
            rw [pair_symm] at hab
            exact star_eq_zero.mp hab
  exact ⟨hTight, hSpanning, hOrth⟩

end Submissions.CopiesTransversalCore.Core
