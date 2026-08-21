import Mathlib

namespace Submissions.MinUPB344Lower.Parity

set_option maxRecDepth 40000
set_option maxHeartbeats 10000000

open Finset

def ip {d : ℕ} (x y : Fin d → ℂ) : ℂ := ∑ r, star (x r) * y r

lemma ip_conj {d : ℕ} (x y : Fin d → ℂ) : star (ip x y) = ip y x := by
  simp [ip, star_sum, mul_comm]

lemma ip_eq_zero_comm {d : ℕ} {x y : Fin d → ℂ} : ip x y = 0 ↔ ip y x = 0 := by
  constructor <;> intro h
  · rw [← ip_conj, h, star_zero]
  · rw [← ip_conj, h, star_zero]

lemma ip_self_ne_zero {d : ℕ} {x : Fin d → ℂ} (hx : x ≠ 0) : ip x x ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r, x r ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have key : ∀ r : Fin d, star (x r) * x r = ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have h := RCLike.conj_mul (K := ℂ) (x r)
    push_cast
    simpa using h
  have hsum : ip x x = ((∑ r, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  rw [hsum]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => sq_nonneg ‖x r‖)).1 hzero
  have hn : ‖x r₀‖ = 0 := by
    have h2 := hall r₀ (Finset.mem_univ r₀)
    nlinarith [norm_nonneg (x r₀)]
  exact hr₀ (norm_eq_zero.1 hn)

def ipMap {d m : ℕ} (z : Fin m → Fin d → ℂ) (T : Finset (Fin m)) :
    (Fin d → ℂ) →ₗ[ℂ] (T → ℂ) where
  toFun c := fun l => ip (z l.1) c
  map_add' c c' := by
    funext l
    simp [ip, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext l
    simp [ip, Finset.mul_sum, mul_left_comm]

lemma exists_kernel_vec {d m : ℕ} (z : Fin m → Fin d → ℂ) (T : Finset (Fin m))
    (hcard : T.card < d) :
    ∃ c : Fin d → ℂ, c ≠ 0 ∧ ∀ l ∈ T, ip (z l) c = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (ipMap z T) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hne
    obtain ⟨l, hlT, hl⟩ := hcon c hne
    have hzero : (ipMap z T) c ⟨l, hlT⟩ = 0 := by
      rw [LinearMap.mem_ker] at hc
      rw [hc]
      rfl
    exact hl hzero
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
  omega

lemma even_card_of_involutive {α : Type*} [DecidableEq α] (f : α → α)
    (hff : ∀ x, f (f x) = x) :
    ∀ s : Finset α, (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f x ≠ x) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hcl hneS
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hfa : f a ∈ s := hcl a ha
      have hfa' : f a ∈ s.erase a := Finset.mem_erase.2 ⟨hneS a ha, hfa⟩
      set t := (s.erase a).erase (f a) with ht
      have hts : t ⊆ s :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hat : a ∉ t := by
        simp [ht, Finset.mem_erase]
      have hsub : t ⊂ s := ⟨hts, fun h => hat (h ha)⟩
      have hclt : ∀ x ∈ t, f x ∈ t := by
        intro x hx
        rw [ht, Finset.mem_erase, Finset.mem_erase] at hx
        obtain ⟨hxfa, hxa, hxs⟩ := hx
        rw [ht, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hcl x hxs⟩
        · intro h
          exact hxa (by rw [← hff x, h, hff a])
        · intro h
          exact hxfa (by rw [← hff x, h])
      have hnet : ∀ x ∈ t, f x ≠ x := by
        intro x hx
        exact hneS x (hts hx)
      have hev := ih t hsub hclt hnet
      have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      have h2 : t.card = (s.erase a).card - 1 := Finset.card_erase_of_mem hfa'
      have hs1 : 1 ≤ s.card := Finset.card_pos.2 ⟨a, ha⟩
      have hs2 : 1 ≤ (s.erase a).card := Finset.card_pos.2 ⟨f a, hfa'⟩
      have : s.card = t.card + 2 := by omega
      rw [this]
      exact hev.add (even_two)

theorem proof :
    ∀ m : ℕ, m ≤ 9 →
    ¬ ∃ u : Fin m → Fin 3 → ℂ,
      ∃ w : Fin m → Fin 4 → ℂ,
      ∃ z : Fin m → Fin 4 → ℂ,
        (∀ i, u i ≠ 0) ∧
        (∀ i, w i ≠ 0) ∧
        (∀ i, z i ≠ 0) ∧
        (∀ i j, i ≠ j →
          (∑ r, star (u i r) * u j r) *
          (∑ r, star (w i r) * w j r) *
          (∑ r, star (z i r) * z j r) = 0) ∧
        (∀ a : Fin 3 → ℂ, a ≠ 0 → ∀ b : Fin 4 → ℂ, b ≠ 0 →
          ∀ c : Fin 4 → ℂ, c ≠ 0 →
          ∃ i,
            (∑ r, star (u i r) * a r) *
            (∑ r, star (w i r) * b r) *
            (∑ r, star (z i r) * c r) ≠ 0) := by
  intro m hm
  rintro ⟨u, w, z, hu, hw, hz, horth, hunext⟩
  classical
  by_cases hm8 : m ≤ 8
  · let T1 : Finset (Fin m) := Finset.univ.filter (fun i => i.val < 2)
    let T2 : Finset (Fin m) := Finset.univ.filter (fun i => 2 ≤ i.val ∧ i.val < 5)
    let T3 : Finset (Fin m) := Finset.univ.filter (fun i => 5 ≤ i.val)
    have hT1 : T1.card ≤ 2 := by
      apply Finset.card_le_card_of_injOn (s := T1) (t := Finset.range 2)
        (fun i : Fin m => i.val)
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi |>.2)
      · intro a ha b hb hab
        exact Fin.ext hab
    have hT2 : T2.card ≤ 3 := by
      apply Finset.card_le_card_of_injOn (s := T2) (t := Finset.Icc 2 4)
        (fun i : Fin m => i.val)
      · intro i hi
        have hh := Finset.mem_filter.mp hi |>.2
        exact Finset.mem_Icc.mpr ⟨hh.1, Nat.le_of_lt_succ hh.2⟩
      · intro a ha b hb hab
        exact Fin.ext hab
    have hT3 : T3.card ≤ 3 := by
      apply Finset.card_le_card_of_injOn (s := T3) (t := Finset.Icc 5 7)
        (fun i : Fin m => i.val)
      · intro i hi
        have hh := Finset.mem_filter.mp hi |>.2
        have hil : i.val < m := i.isLt
        have hil8 : i.val < 8 := lt_of_lt_of_le hil hm8
        have hi7 : i.val ≤ 7 := by omega
        exact Finset.mem_Icc.mpr ⟨hh, hi7⟩
      · intro a ha b hb hab
        exact Fin.ext hab
    obtain ⟨a, ha0, ha⟩ := exists_kernel_vec u T1 (by omega)
    obtain ⟨b, hb0, hb⟩ := exists_kernel_vec w T2 (by omega)
    obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z T3 (by omega)
    obtain ⟨i, hi⟩ := hunext a ha0 b hb0 c hc0
    have hparts : i ∈ T1 ∨ i ∈ T2 ∨ i ∈ T3 := by
      by_cases h1 : i.val < 2
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩)
      · by_cases h2 : i.val < 5
        · exact Or.inr (Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, by omega⟩))
        · exact Or.inr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, by omega⟩))
    rcases hparts with hi1 | hi2 | hi3
    · exact hi (by
        change ip (u i) a * ip (w i) b * ip (z i) c = 0
        rw [ha i hi1]
        simp)
    · exact hi (by
        change ip (u i) a * ip (w i) b * ip (z i) c = 0
        rw [hb i hi2]
        simp)
    · exact hi (by
        change ip (u i) a * ip (w i) b * ip (z i) c = 0
        rw [hc i hi3]
        simp)
  · have hm9 : m = 9 := by omega
    subst m
    have hAcard : ∀ a : Fin 3 → ℂ, a ≠ 0 →
        (Finset.univ.filter (fun l => ip (u l) a = 0)).card ≤ 2 := by
      intro a ha
      by_contra hgt
      let A := Finset.univ.filter (fun l => ip (u l) a = 0)
      let R := Finset.univ \ A
      have hA3 : 3 ≤ A.card := by
        simpa [A] using
          (show 3 ≤ (Finset.univ.filter (fun l => ip (u l) a = 0)).card by omega)
      have hRle : R.card ≤ 6 := by
        have hAR : A.card + R.card = 9 := by
          change (Finset.univ.filter (fun l => ip (u l) a = 0)).card +
              (Finset.univ \ Finset.univ.filter (fun l => ip (u l) a = 0)).card = 9
          rw [Finset.card_sdiff,
            Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
          have hAle : (Finset.univ.filter (fun l => ip (u l) a = 0)).card ≤ 9 := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          simp
          omega
        omega
      obtain ⟨S, hSR, hScard, hRS⟩ : ∃ S : Finset (Fin 9), S ⊆ R ∧
          S.card ≤ 3 ∧ (R \ S).card ≤ 3 := by
        by_cases h3 : 3 ≤ R.card
        · obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq h3
          refine ⟨S, hSR, by omega, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSR]
          omega
        · refine ⟨∅, by simp, by simp, ?_⟩
          simp
          omega
      obtain ⟨b, hb0, hb⟩ := exists_kernel_vec w S (by omega)
      obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z (R \ S) (by omega)
      obtain ⟨i, hi⟩ := hunext a ha b hb0 c hc0
      have hkill : ip (u i) a = 0 ∨ ip (w i) b = 0 ∨ ip (z i) c = 0 := by
        by_cases hiA : i ∈ A
        · exact Or.inl (Finset.mem_filter.mp hiA).2
        · have hiR : i ∈ R := by
            change i ∈ Finset.univ \ A
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiA⟩
          by_cases hiS : i ∈ S
          · exact Or.inr (Or.inl (hb i hiS))
          · exact Or.inr (Or.inr (hc i (Finset.mem_sdiff.mpr ⟨hiR, hiS⟩)))
      rcases hkill with hkill | hkill | hkill
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
    have hBcard : ∀ b : Fin 4 → ℂ, b ≠ 0 →
        (Finset.univ.filter (fun l => ip (w l) b = 0)).card ≤ 3 := by
      intro b hb
      by_contra hgt
      let B := Finset.univ.filter (fun l => ip (w l) b = 0)
      let R := Finset.univ \ B
      have hB4 : 4 ≤ B.card := by
        simpa [B] using
          (show 4 ≤ (Finset.univ.filter (fun l => ip (w l) b = 0)).card by omega)
      have hRle : R.card ≤ 5 := by
        have hBR : B.card + R.card = 9 := by
          change (Finset.univ.filter (fun l => ip (w l) b = 0)).card +
              (Finset.univ \ Finset.univ.filter (fun l => ip (w l) b = 0)).card = 9
          rw [Finset.card_sdiff,
            Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
          have hBle : (Finset.univ.filter (fun l => ip (w l) b = 0)).card ≤ 9 := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          simp
          omega
        omega
      obtain ⟨S, hSR, hScard, hRS⟩ : ∃ S : Finset (Fin 9), S ⊆ R ∧
          S.card ≤ 2 ∧ (R \ S).card ≤ 3 := by
        by_cases h2 : 2 ≤ R.card
        · obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq h2
          refine ⟨S, hSR, by omega, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSR]
          omega
        · refine ⟨∅, by simp, by simp, ?_⟩
          simp
          omega
      obtain ⟨a, ha0, ha⟩ := exists_kernel_vec u S (by omega)
      obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z (R \ S) (by omega)
      obtain ⟨i, hi⟩ := hunext a ha0 b hb c hc0
      have hkill : ip (w i) b = 0 ∨ ip (u i) a = 0 ∨ ip (z i) c = 0 := by
        by_cases hiB : i ∈ B
        · exact Or.inl (Finset.mem_filter.mp hiB).2
        · have hiR : i ∈ R := by
            change i ∈ Finset.univ \ B
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiB⟩
          by_cases hiS : i ∈ S
          · exact Or.inr (Or.inl (ha i hiS))
          · exact Or.inr (Or.inr (hc i (Finset.mem_sdiff.mpr ⟨hiR, hiS⟩)))
      rcases hkill with hkill | hkill | hkill
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
    have hCcard : ∀ c : Fin 4 → ℂ, c ≠ 0 →
        (Finset.univ.filter (fun l => ip (z l) c = 0)).card ≤ 3 := by
      intro c hc
      by_contra hgt
      let C := Finset.univ.filter (fun l => ip (z l) c = 0)
      let R := Finset.univ \ C
      have hC4 : 4 ≤ C.card := by
        simpa [C] using
          (show 4 ≤ (Finset.univ.filter (fun l => ip (z l) c = 0)).card by omega)
      have hRle : R.card ≤ 5 := by
        have hCR : C.card + R.card = 9 := by
          change (Finset.univ.filter (fun l => ip (z l) c = 0)).card +
              (Finset.univ \ Finset.univ.filter (fun l => ip (z l) c = 0)).card = 9
          rw [Finset.card_sdiff,
            Finset.inter_eq_left.2 (Finset.filter_subset _ _)]
          have hCle : (Finset.univ.filter (fun l => ip (z l) c = 0)).card ≤ 9 := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          simp
          omega
        omega
      obtain ⟨S, hSR, hScard, hRS⟩ : ∃ S : Finset (Fin 9), S ⊆ R ∧
          S.card ≤ 2 ∧ (R \ S).card ≤ 3 := by
        by_cases h2 : 2 ≤ R.card
        · obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq h2
          refine ⟨S, hSR, by omega, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSR]
          omega
        · refine ⟨∅, by simp, by simp, ?_⟩
          simp
          omega
      obtain ⟨a, ha0, ha⟩ := exists_kernel_vec u S (by omega)
      obtain ⟨b, hb0, hb⟩ := exists_kernel_vec w (R \ S) (by omega)
      obtain ⟨i, hi⟩ := hunext a ha0 b hb0 c hc
      have hkill : ip (z i) c = 0 ∨ ip (u i) a = 0 ∨ ip (w i) b = 0 := by
        by_cases hiC : i ∈ C
        · exact Or.inl (Finset.mem_filter.mp hiC).2
        · have hiR : i ∈ R := by
            change i ∈ Finset.univ \ C
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiC⟩
          by_cases hiS : i ∈ S
          · exact Or.inr (Or.inl (ha i hiS))
          · exact Or.inr (Or.inr (hb i (Finset.mem_sdiff.mpr ⟨hiR, hiS⟩)))
      rcases hkill with hkill | hkill | hkill
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
      · exact hi (by
          change ip (u i) a * ip (w i) b * ip (z i) c = 0
          rw [hkill]
          simp)
    have hBexact : ∀ i : Fin 9,
        ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).card = 3 := by
      intro i
      let A := (Finset.univ.erase i).filter (fun l => ip (u l) (u i) = 0)
      let B := (Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)
      let C := (Finset.univ.erase i).filter (fun l => ip (z l) (z i) = 0)
      have hAi : A.card ≤ 2 := by
        apply le_trans (Finset.card_le_card ?_) (hAcard (u i) (hu i))
        intro l hl
        simp only [A, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hBi : B.card ≤ 3 := by
        apply le_trans (Finset.card_le_card ?_) (hBcard (w i) (hw i))
        intro l hl
        simp only [B, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hCi : C.card ≤ 3 := by
        apply le_trans (Finset.card_le_card ?_) (hCcard (z i) (hz i))
        intro l hl
        simp only [C, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hcover : Finset.univ.erase i ⊆ A ∪ B ∪ C := by
        intro l hl
        have hli : l ≠ i := (Finset.mem_erase.mp hl).1
        rcases mul_eq_zero.mp (horth i l (Ne.symm hli)) with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hl,
                (ip_eq_zero_comm (x := u i) (y := u l)).mp h⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hl,
                (ip_eq_zero_comm (x := w i) (y := w l)).mp h⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hl,
              (ip_eq_zero_comm (x := z i) (y := z l)).mp h⟩)
      have hlow : 8 ≤ A.card + B.card + C.card := by
        have hle : 8 ≤ (A ∪ B ∪ C).card := by
          have := Finset.card_le_card hcover
          simpa using this
        have hab := Finset.card_union_le A B
        have habc := Finset.card_union_le (A ∪ B) C
        omega
      have hAfull : (Finset.univ.filter (fun l => ip (u l) (u i) = 0)).card ≤ 2 :=
        hAcard (u i) (hu i)
      have hCfull : (Finset.univ.filter (fun l => ip (z l) (z i) = 0)).card ≤ 3 :=
        hCcard (z i) (hz i)
      have hAembed : A.card ≤
          (Finset.univ.filter (fun l => ip (u l) (u i) = 0)).card := by
        apply Finset.card_le_card
        intro l hl
        simp only [A, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      have hCembed : C.card ≤
          (Finset.univ.filter (fun l => ip (z l) (z i) = 0)).card := by
        apply Finset.card_le_card
        intro l hl
        simp only [C, Finset.mem_filter] at hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.2⟩
      change B.card = 3
      omega
    let F : Fin 9 → Finset (Fin 9 × Fin 9) := fun i =>
      ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
        (fun l => (i, l))
    let E : Finset (Fin 9 × Fin 9) := Finset.univ.biUnion F
    have hFcard : ∀ i : Fin 9, (F i).card = 3 := by
      intro i
      change (((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
        (fun l => (i, l))).card = 3
      rw [Finset.card_image_iff.mpr]
      · exact hBexact i
      · intro a ha b hb hab
        exact congrArg Prod.snd hab
    have hEcard : E.card = 27 := by
      change (Finset.univ.biUnion F).card = 27
      rw [Finset.card_biUnion]
      · simp [hFcard]
      · intro i hi j hj hij
        apply Finset.disjoint_left.2
        intro p hpi hpj
        change p ∈
          ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
            (fun l => (i, l)) at hpi
        change p ∈
          ((Finset.univ.erase j).filter (fun l => ip (w l) (w j) = 0)).image
            (fun l => (j, l)) at hpj
        rcases Finset.mem_image.mp hpi with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hpj with ⟨b, hb, hab⟩
        simp only [Prod.mk.injEq] at hab
        exact hij hab.1.symm
    have hEclosed : ∀ p ∈ E, (p.2, p.1) ∈ E := by
      intro p hp
      change p ∈ Finset.univ.biUnion F at hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      change p ∈
        ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
          (fun l => (i, l)) at hpi
      rcases Finset.mem_image.mp hpi with ⟨j, hj, rfl⟩
      have hji : j ≠ i := by
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
      have hzero : ip (w j) (w i) = 0 := (Finset.mem_filter.mp hj).2
      have hzero' : ip (w i) (w j) = 0 :=
        (ip_eq_zero_comm (x := w j) (y := w i)).mp hzero
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ j, ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩, hzero'⟩, rfl⟩
    have hEven : Even E.card := by
      apply even_card_of_involutive (fun p : Fin 9 × Fin 9 => (p.2, p.1))
      · intro p
        cases p
        rfl
      · exact hEclosed
      · intro p hp hsame
        have hbi := Finset.mem_biUnion.mp hp
        obtain ⟨i, hi, hpi⟩ := hbi
        change p ∈
          ((Finset.univ.erase i).filter (fun l => ip (w l) (w i) = 0)).image
            (fun l => (i, l)) at hpi
        rcases Finset.mem_image.mp hpi with ⟨j, hj, rfl⟩
        have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
        have hpair : j = i ∧ i = j := by
          simpa [Prod.ext_iff] using hsame
        have hji : j = i := hpair.1
        exact hne hji
    rw [hEcard] at hEven
    norm_num at hEven

end Submissions.MinUPB344Lower.Parity
