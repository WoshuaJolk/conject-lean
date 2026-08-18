import Mathlib

namespace Submissions.OVHypForcesInjective.WoshuaJolk

open Finset

def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

theorem proof :
    ∀ (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)),
      2 ≤ t → t ≤ k → t ≤ m → OVHyp k t m n A →
        ∀ j : Fin k, Function.Injective (A j) := by
  classical
  intro k t m n A ht2 htk htm hOV j i₁ i₂ hA
  by_contra hne
  have hj : (j : ℕ) < k := j.isLt
  -- Step 1: a set `V` with `i₂ ∈ V`, `i₁ ∉ V`, `V.card = t - 1`.
  have hcard2 : ({i₁, i₂} : Finset (Fin m)).card = 2 :=
    Finset.card_pair_eq_two_iff.2 hne
  have hcs : ((univ : Finset (Fin m)) \ {i₁, i₂}).card = m - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard2, Finset.card_univ,
      Fintype.card_fin]
  have hle : t - 2 ≤ ((univ : Finset (Fin m)) \ {i₁, i₂}).card := by omega
  obtain ⟨V₀, hV₀sub, hV₀card⟩ := Finset.exists_subset_card_eq hle
  have hi₂V₀ : i₂ ∉ V₀ := by
    intro h
    have := hV₀sub h
    simp at this
  have hi₁V₀ : i₁ ∉ V₀ := by
    intro h
    have := hV₀sub h
    simp at this
  obtain ⟨V, hVcard, hi₂V, hi₁V⟩ :
      ∃ V : Finset (Fin m), V.card = t - 1 ∧ i₂ ∈ V ∧ i₁ ∉ V := by
    refine ⟨insert i₂ V₀, ?_, Finset.mem_insert_self _ _, ?_⟩
    · rw [Finset.card_insert_of_notMem hi₂V₀, hV₀card]
      omega
    · simp [hne, hi₁V₀]
  -- Step 2: an enumeration `q : ℕ → Fin m` of `V`.
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℕ → Fin m, (∀ x, q x ∈ V) ∧
      ∀ v ∈ V, ∃ x ≤ t - 2, q x = v := by
    have hb : ∀ x : ℕ, min x (t - 2) < t - 1 := by omega
    refine ⟨fun x => (((V.equivFinOfCardEq hVcard).symm ⟨min x (t - 2), hb x⟩ :
        {y // y ∈ V}) : Fin m), fun x => ((V.equivFinOfCardEq hVcard).symm _).2, ?_⟩
    intro v hv
    refine ⟨((V.equivFinOfCardEq hVcard) ⟨v, hv⟩ : ℕ), by
      have := ((V.equivFinOfCardEq hVcard) ⟨v, hv⟩).isLt; omega, ?_⟩
    have hEq : (V.equivFinOfCardEq hVcard).symm
        ⟨min ((V.equivFinOfCardEq hVcard) ⟨v, hv⟩ : ℕ) (t - 2),
          hb ((V.equivFinOfCardEq hVcard) ⟨v, hv⟩ : ℕ)⟩ = ⟨v, hv⟩ := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      have := ((V.equivFinOfCardEq hVcard) ⟨v, hv⟩).isLt
      show min ((V.equivFinOfCardEq hVcard) ⟨v, hv⟩ : ℕ) (t - 2)
          = ((V.equivFinOfCardEq hVcard) ⟨v, hv⟩ : ℕ)
      omega
    exact congrArg Subtype.val hEq
  -- Step 3: the two maps `f` and `g`.
  obtain ⟨f, hfj, hfne⟩ : ∃ f : Fin k → Fin m, f j = i₁ ∧
      ∀ j', j' ≠ j → f j' = q (min (if (j' : ℕ) < (j : ℕ) then (j' : ℕ)
        else (j' : ℕ) - 1) (t - 2)) := by
    refine ⟨fun j' => if j' = j then i₁ else
      q (min (if (j' : ℕ) < (j : ℕ) then (j' : ℕ) else (j' : ℕ) - 1) (t - 2)),
      by simp, ?_⟩
    intro j' h
    simp [h]
  obtain ⟨g, hgj, hgne⟩ : ∃ g : Fin k → Fin m, g j = i₂ ∧ ∀ j', j' ≠ j → g j' = f j' :=
    ⟨fun j' => if j' = j then i₂ else f j', by simp, by intro j' h; simp [h]⟩
  -- Step 4: every element of `V` is hit by `f` at a coordinate other than `j`.
  have hhit : ∀ v ∈ V, ∃ j' : Fin k, j' ≠ j ∧ f j' = v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hq2 v hv
    have hkb : (if x < (j : ℕ) then x else x + 1) < k := by split_ifs <;> omega
    have hne' : (⟨if x < (j : ℕ) then x else x + 1, hkb⟩ : Fin k) ≠ j := by
      intro h
      have h2 : (if x < (j : ℕ) then x else x + 1) = (j : ℕ) := congrArg Fin.val h
      split_ifs at h2 <;> omega
    refine ⟨⟨if x < (j : ℕ) then x else x + 1, hkb⟩, hne', ?_⟩
    rw [hfne _ hne']
    refine congrArg q ?_
    show min (if (if x < (j : ℕ) then x else x + 1) < (j : ℕ) then
        (if x < (j : ℕ) then x else x + 1)
      else (if x < (j : ℕ) then x else x + 1) - 1) (t - 2) = x
    split_ifs <;> omega
  -- Step 5: the images.
  have himf : image f univ = insert i₁ V := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hy
      by_cases h : j' = j
      · subst h
        rw [hfj]
        exact Finset.mem_insert_self _ _
      · rw [hfne j' h]
        exact Finset.mem_insert_of_mem (hq1 _)
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hv
      · exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hfj⟩
      · obtain ⟨j', -, hfj'⟩ := hhit y hv
        exact Finset.mem_image.2 ⟨j', Finset.mem_univ _, hfj'⟩
  have himg : image g univ = V := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hy
      by_cases h : j' = j
      · subst h
        rw [hgj]
        exact hi₂V
      · rw [hgne j' h, hfne j' h]
        exact hq1 _
    · intro y hy
      obtain ⟨j', hne', hfj'⟩ := hhit y hy
      exact Finset.mem_image.2 ⟨j', Finset.mem_univ _, by rw [hgne j' hne', hfj']⟩
  have hcf : (image f univ).card = t := by
    rw [himf, Finset.card_insert_of_notMem hi₁V, hVcard]
    omega
  have hcg : (image g univ).card = t - 1 := by rw [himg, hVcard]
  -- Step 6: `f` and `g` have the same intersection.
  have hkey : kInter A f = kInter A g := by
    have hpt : ∀ j' : Fin k, A j' (f j') = A j' (g j') := by
      intro j'
      by_cases h : j' = j
      · subst h
        rw [hfj, hgj, hA]
      · rw [hgne j' h]
    ext x
    simp only [kInter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j'
      rw [← hpt j']
      exact h j'
    · intro h j'
      rw [hpt j']
      exact h j'
  have h1 : Even (kInter A f).card := (hOV f).2 hcf.ge
  have h2 : ¬ Even (kInter A g).card := by
    intro h
    have h3 := (hOV g).1 h
    rw [hcg] at h3
    omega
  rw [hkey] at h1
  exact h2 h1

end Submissions.OVHypForcesInjective.WoshuaJolk
