import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Map

/-!
Route: push the family into the quotient `M ⧸ K.subgroupOf M`, where distinct cosets of `K`
with representatives in `M` stay distinct, then apply Lagrange in the form
`Nat.card (K.subgroupOf M) * (K.subgroupOf M).index = Nat.card M` together with
`K.subgroupOf M ≃* K`. No enumeration and no decidability is used.
-/

namespace Submissions.DisjointCosetBudget.CosetIndexCount

theorem proof :
    ∀ (G : Type) [Group G] [Finite G] (K M : Subgroup G), K ≤ M →
      ∀ C : Finset (G ⧸ K),
        (∀ q ∈ C, ∃ g : G, g ∈ M ∧ q = (g : G ⧸ K)) →
        ((1 : G) : G ⧸ K) ∉ C →
        (C.card + 1) * Nat.card K ≤ Nat.card M := by
  classical
  intro G _ _ K M hKM C hrep hhole
  have : Fintype (M ⧸ K.subgroupOf M) := Fintype.ofFinite _
  set C' : Finset (G ⧸ K) := insert ((1 : G) : G ⧸ K) C with hC'def
  have hC'card : C'.card = C.card + 1 := by
    rw [hC'def, Finset.card_insert_of_notMem hhole]
  have hrep' : ∀ q ∈ C', ∃ x : G, x ∈ M ∧ q = (x : G ⧸ K) := by
    intro q hq
    rcases Finset.mem_insert.1 hq with h | h
    · exact ⟨1, one_mem M, h⟩
    · exact hrep q h
  choose! r hr using hrep'
  set φ : G ⧸ K → M ⧸ K.subgroupOf M := fun q =>
    if h : r q ∈ M then ((⟨r q, h⟩ : M) : M ⧸ K.subgroupOf M)
    else ((1 : M) : M ⧸ K.subgroupOf M) with hφdef
  have hinj : ∀ q₁ ∈ C', ∀ q₂ ∈ C', φ q₁ = φ q₂ → q₁ = q₂ := by
    intro q₁ h₁ q₂ h₂ heq
    obtain ⟨hM₁, hq₁⟩ := hr q₁ h₁
    obtain ⟨hM₂, hq₂⟩ := hr q₂ h₂
    rw [hφdef] at heq
    simp only [dif_pos hM₁, dif_pos hM₂] at heq
    have hmem : (⟨r q₁, hM₁⟩ : M)⁻¹ * (⟨r q₂, hM₂⟩ : M) ∈ K.subgroupOf M :=
      (QuotientGroup.eq (s := K.subgroupOf M)).1 heq
    have hK : (r q₁)⁻¹ * r q₂ ∈ K := by
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hq : ((r q₁ : G) : G ⧸ K) = ((r q₂ : G) : G ⧸ K) :=
      (QuotientGroup.eq (s := K)).2 hK
    rw [hq₁, hq₂]; exact hq
  have hle : C'.card ≤ Fintype.card (M ⧸ K.subgroupOf M) := by
    have := Finset.card_le_card_of_injOn φ (fun a _ => Finset.mem_univ (φ a)) hinj
    simpa [Finset.card_univ] using this
  have hidx : Nat.card (K.subgroupOf M) * (K.subgroupOf M).index = Nat.card M :=
    Subgroup.card_mul_index _
  have hcardK : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hindex : (K.subgroupOf M).index = Fintype.card (M ⧸ K.subgroupOf M) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  have h1 : C'.card ≤ (K.subgroupOf M).index := by rw [hindex]; exact hle
  rw [hcardK] at hidx
  have key : Nat.card K * C'.card ≤ Nat.card M := by
    rw [← hidx]
    exact Nat.mul_le_mul (le_refl (Nat.card K)) h1
  rw [hC'card, Nat.mul_comm] at key
  exact key

end Submissions.DisjointCosetBudget.CosetIndexCount
