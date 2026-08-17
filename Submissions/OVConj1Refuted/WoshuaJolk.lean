import Mathlib

namespace Submissions.OVConj1Refuted.WoshuaJolk

open Finset

/-! ## Canonical definitions (copied verbatim from the statement) -/

def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-! ## Generic helpers -/

lemma filter_disjSum {α β : Type*} (s : Finset α) (t : Finset β)
    (p : α ⊕ β → Prop) [DecidablePred p] :
    (s.disjSum t).filter p
      = (s.filter fun a => p (Sum.inl a)).disjSum (t.filter fun b => p (Sum.inr b)) := by
  ext x
  cases x <;> simp

lemma card_filter_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : α ⊕ β → Prop) [DecidablePred p] :
    ((univ : Finset (α ⊕ β)).filter p).card
      = ((univ : Finset α).filter fun a => p (Sum.inl a)).card
        + ((univ : Finset β).filter fun b => p (Sum.inr b)).card := by
  rw [← Finset.univ_disjSum_univ, filter_disjSum, Finset.card_disjSum]

/-! ## Arithmetic of `choose 2` -/

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  have h1 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
  rw [h1, Nat.choose_one_right, Nat.add_comm]

lemma two_choose_two (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [choose_two_succ]
      have h : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h, ← ih]
      ring

lemma choose_two_mod_four (J r : ℕ) : (4 * J + r).choose 2 % 2 = r.choose 2 % 2 := by
  induction J with
  | zero => simp
  | succ K ih =>
      have h4 : 4 * (K + 1) + r = 4 * K + r + 1 + 1 + 1 + 1 := by ring
      rw [h4, choose_two_succ, choose_two_succ, choose_two_succ, choose_two_succ]
      omega

/-! ## The construction -/

/-- Two-element subsets of `Fin M`. -/
abbrev Pr (M : ℕ) : Type := {T : Finset (Fin M) // T.card = 2}

/-- Ground set: two copies of the 2-subsets, plus one extra point. -/
abbrev Gr (M : ℕ) : Type := Pr M ⊕ (Pr M ⊕ Unit)

/-- `i` belongs to the set `F i` at the ground element `x`. -/
def memF {M : ℕ} (i : Fin M) : Gr M → Bool
  | Sum.inl T => decide (i ∈ T.val)
  | Sum.inr (Sum.inl T) => decide (i ∉ T.val)
  | Sum.inr (Sum.inr _) => true

/-- The set `F i` inside the ground type. -/
def Fset {M : ℕ} (i : Fin M) : Finset (Gr M) :=
  (univ : Finset (Gr M)).filter (fun x => memF i x = true)

/-- The intersection `⋂_{i ∈ S} F i`. -/
def bigI {M : ℕ} (S : Finset (Fin M)) : Finset (Gr M) :=
  (univ : Finset (Gr M)).filter (fun x => ∀ i ∈ S, memF i x = true)

lemma memF_inl {M : ℕ} (i : Fin M) (T : Pr M) :
    (memF i (Sum.inl T) = true) ↔ i ∈ T.val := by simp [memF]

lemma memF_inrl {M : ℕ} (i : Fin M) (T : Pr M) :
    (memF i (Sum.inr (Sum.inl T)) = true) ↔ i ∉ T.val := by simp [memF]

lemma memF_inrr {M : ℕ} (i : Fin M) (u : Unit) :
    memF i (Sum.inr (Sum.inr u)) = true := rfl

/-! ## The cardinality identity -/

lemma card_bigI_decomp {M : ℕ} (S : Finset (Fin M)) :
    (bigI S).card
      = ((univ : Finset (Pr M)).filter fun T => S ⊆ T.val).card
        + (((univ : Finset (Pr M)).filter fun T => ∀ i ∈ S, i ∉ T.val).card + 1) := by
  rw [bigI, card_filter_sum, card_filter_sum]
  congr 1
  · refine congrArg Finset.card (Finset.filter_congr ?_)
    intro T _
    simp [memF_inl, Finset.subset_iff]
  · congr 1
    · refine congrArg Finset.card (Finset.filter_congr ?_)
      intro T _
      simp [memF_inrl]
    · rw [Finset.filter_true_of_mem, card_univ]
      · simp
      · intro u _ i _
        exact memF_inrr i u

lemma card_pr_avoid {M : ℕ} (S : Finset (Fin M)) :
    ((univ : Finset (Pr M)).filter fun T => ∀ i ∈ S, i ∉ T.val).card
      = (M - S.card).choose 2 := by
  have h : ((univ : Finset (Pr M)).filter fun T => ∀ i ∈ S, i ∉ T.val).card
      = (powersetCard 2 ((univ : Finset (Fin M)) \ S)).card := by
    apply Finset.card_bij (fun T _ => T.val)
    · intro T hT
      simp only [mem_filter, mem_univ, true_and] at hT
      simp only [mem_powersetCard]
      refine ⟨?_, T.2⟩
      intro x hx
      simp only [mem_sdiff, mem_univ, true_and]
      intro hxS
      exact hT x hxS hx
    · intro T1 _ T2 _ hh
      exact Subtype.ext hh
    · intro T hT
      simp only [mem_powersetCard] at hT
      refine ⟨⟨T, hT.2⟩, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      intro i hiS hiT
      have hx := hT.1 hiT
      simp only [mem_sdiff, mem_univ, true_and] at hx
      exact hx hiS
  have hcs : ((univ : Finset (Fin M)) \ S).card = M - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, card_univ, Fintype.card_fin]
  rw [h, card_powersetCard, hcs]

lemma card_pr_contain_ge3 {M : ℕ} (S : Finset (Fin M)) (h : 3 ≤ S.card) :
    ((univ : Finset (Pr M)).filter fun T => S ⊆ T.val).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro T _ hsub
  have hc := Finset.card_le_card hsub
  rw [T.2] at hc
  omega

lemma card_pr_contain_eq2 {M : ℕ} (S : Finset (Fin M)) (h : S.card = 2) :
    ((univ : Finset (Pr M)).filter fun T => S ⊆ T.val).card = 1 := by
  have he : ((univ : Finset (Pr M)).filter fun T => S ⊆ T.val) = {(⟨S, h⟩ : Pr M)} := by
    ext T
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hsub
      refine (Subtype.ext ?_)
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [T.2, h])).symm
    · rintro rfl
      exact subset_rfl
  rw [he, card_singleton]

lemma card_pr_total (M : ℕ) : Fintype.card (Pr M) = M.choose 2 := by
  simp

lemma card_bigI_singleton {M : ℕ} (i : Fin M) :
    (bigI ({i} : Finset (Fin M))).card = M.choose 2 + 1 := by
  rw [card_bigI_decomp]
  have e1 : ((univ : Finset (Pr M)).filter fun T => ({i} : Finset (Fin M)) ⊆ T.val)
      = ((univ : Finset (Pr M)).filter fun T => i ∈ T.val) := by
    apply Finset.filter_congr
    intro T _
    simp [Finset.singleton_subset_iff]
  have e2 : ((univ : Finset (Pr M)).filter fun T => ∀ j ∈ ({i} : Finset (Fin M)), j ∉ T.val)
      = ((univ : Finset (Pr M)).filter fun T => ¬ (i ∈ T.val)) := by
    apply Finset.filter_congr
    intro T _
    simp
  rw [e1, e2]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Pr M))) (p := fun T : Pr M => i ∈ T.val)
  rw [card_univ, card_pr_total] at hsum
  omega

lemma card_bigI_eq2 {M : ℕ} (S : Finset (Fin M)) (h : S.card = 2) :
    (bigI S).card = (M - 2).choose 2 + 2 := by
  rw [card_bigI_decomp, card_pr_contain_eq2 S h, card_pr_avoid, h]
  omega

lemma card_bigI_ge3 {M : ℕ} (S : Finset (Fin M)) (h : 3 ≤ S.card) :
    (bigI S).card = (M - S.card).choose 2 + 1 := by
  rw [card_bigI_decomp, card_pr_contain_ge3 S h, card_pr_avoid]
  omega

/-! ## Parity -/

lemma parity_main (J : ℕ) (S : Finset (Fin (4 * J + 8)))
    (h1 : 1 ≤ S.card) (h6 : S.card ≤ 6) :
    (Even (bigI S).card ↔ 5 ≤ S.card) := by
  rw [Nat.even_iff]
  have hcases : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 ∨ S.card = 4 ∨ S.card = 5 ∨ S.card = 6 := by
    omega
  rcases hcases with hd | hd | hd | hd | hd | hd
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hd
    subst hi
    rw [card_bigI_singleton]
    have hp : (4 * J + 8).choose 2 % 2 = (8 : ℕ).choose 2 % 2 := choose_two_mod_four J 8
    have h8 : (8 : ℕ).choose 2 = 28 := by decide
    rw [h8] at hp
    simp only [hd]
    omega
  · rw [card_bigI_eq2 S hd]
    have hM : 4 * J + 8 - 2 = 4 * J + 6 := by omega
    rw [hM]
    have hp : (4 * J + 6).choose 2 % 2 = (6 : ℕ).choose 2 % 2 := choose_two_mod_four J 6
    have h6' : (6 : ℕ).choose 2 = 15 := by decide
    rw [h6'] at hp
    simp only [hd]
    omega
  · rw [card_bigI_ge3 S (by omega), hd]
    have hM : 4 * J + 8 - 3 = 4 * J + 5 := by omega
    rw [hM]
    have hp : (4 * J + 5).choose 2 % 2 = (5 : ℕ).choose 2 % 2 := choose_two_mod_four J 5
    have h5' : (5 : ℕ).choose 2 = 10 := by decide
    rw [h5'] at hp
    omega
  · rw [card_bigI_ge3 S (by omega), hd]
    have hM : 4 * J + 8 - 4 = 4 * J + 4 := by omega
    rw [hM]
    have hp : (4 * J + 4).choose 2 % 2 = (4 : ℕ).choose 2 % 2 := choose_two_mod_four J 4
    have h4' : (4 : ℕ).choose 2 = 6 := by decide
    rw [h4'] at hp
    omega
  · rw [card_bigI_ge3 S (by omega), hd]
    have hM : 4 * J + 8 - 5 = 4 * J + 3 := by omega
    rw [hM]
    have hp : (4 * J + 3).choose 2 % 2 = (3 : ℕ).choose 2 % 2 := choose_two_mod_four J 3
    have h3' : (3 : ℕ).choose 2 = 3 := by decide
    rw [h3'] at hp
    omega
  · rw [card_bigI_ge3 S (by omega), hd]
    have hM : 4 * J + 8 - 6 = 4 * J + 2 := by omega
    rw [hM]
    have hp : (4 * J + 2).choose 2 % 2 = (2 : ℕ).choose 2 % 2 := choose_two_mod_four J 2
    have h2' : (2 : ℕ).choose 2 = 1 := by decide
    rw [h2'] at hp
    omega

/-! ## Transport to `Fin n` -/

lemma card_kInter_eq {M : ℕ} (e : Gr M ≃ Fin (Fintype.card (Gr M))) (f : Fin 6 → Fin M) :
    (kInter (fun (_ : Fin 6) (i : Fin M) => (Fset i).map e.toEmbedding) f).card
      = (bigI (image f univ)).card := by
  have hset : kInter (fun (_ : Fin 6) (i : Fin M) => (Fset i).map e.toEmbedding) f
      = (bigI (image f univ)).map e.toEmbedding := by
    ext x
    simp only [kInter, bigI, Fset, mem_filter, mem_univ, true_and, Finset.mem_map_equiv]
    constructor
    · intro hh i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact hh j
    · intro hh j
      exact hh (f j) (Finset.mem_image_of_mem f (mem_univ j))
  rw [hset, card_map]

lemma card_Gr (M : ℕ) : Fintype.card (Gr M) = 2 * M.choose 2 + 1 := by
  simp [Fintype.card_sum]
  ring

/-! ## The refutation -/

theorem proof : ¬ (∀ k t : ℕ, 2 ≤ t → t ≤ k → k + 2 < 2 * t →
    ∃ C : ℕ, ∀ (n m : ℕ) (A : Fin k → Fin m → Finset (Fin n)),
      OVHyp k t m n A → m ^ (k / 2) ≤ C * n) := by
  intro h
  obtain ⟨C, hC⟩ := h 6 5 (by norm_num) (by norm_num) (by norm_num)
  set M : ℕ := 4 * C + 8 with hM
  set n : ℕ := Fintype.card (Gr M) with hn
  let e : Gr M ≃ Fin (Fintype.card (Gr M)) := Fintype.equivFin (Gr M)
  have hOV : OVHyp 6 5 M n (fun (_ : Fin 6) (i : Fin M) => (Fset i).map e.toEmbedding) := by
    intro f
    rw [card_kInter_eq e f]
    have h1 : 1 ≤ (image f univ).card := by
      rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
      intro hcon
      have : f 0 ∈ image f univ := mem_image_of_mem f (mem_univ 0)
      rw [hcon] at this
      exact absurd this (notMem_empty _)
    have h6 : (image f univ).card ≤ 6 := by
      calc (image f univ).card ≤ (univ : Finset (Fin 6)).card := card_image_le
        _ = 6 := by simp
    exact parity_main C (image f univ) h1 h6
  have hkey := hC n M _ hOV
  norm_num at hkey
  rw [hn, card_Gr] at hkey
  have h2 := two_choose_two M
  have hM8 : 8 ≤ M := by omega
  have hb : 2 * M.choose 2 + 1 ≤ M * M := by
    have hmm : 0 < M := by omega
    nlinarith [h2, hM8]
  have hle : C * (2 * M.choose 2 + 1) ≤ C * (M * M) := Nat.mul_le_mul_left C hb
  have hcube : M ^ 3 = M * (M * M) := by ring
  have hfin : M * (M * M) ≤ C * (M * M) := by
    rw [← hcube]
    exact le_trans hkey hle
  have hpos : 0 < M * M := by positivity
  have hMC : M ≤ C := Nat.le_of_mul_le_mul_right hfin hpos
  omega

end Submissions.OVConj1Refuted.WoshuaJolk
