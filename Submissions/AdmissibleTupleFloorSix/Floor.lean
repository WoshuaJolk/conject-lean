import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.IntervalCases

namespace Submissions.AdmissibleTupleFloorSix.Floor

/-- Admissibility: every prime omits some residue class. -/
def Adm (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r

/-- Pigeonhole: a set with fewer than `p` elements cannot meet every class mod `p`. -/
theorem omit_of_card_lt (T : Finset ℕ) (p : ℕ) (hp : 0 < p) (h : T.card < p) :
    ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r := by
  have hsub : T.image (fun x => x % p) ⊆ Finset.range p := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  have hc : (T.image (fun x => x % p)).card < (Finset.range p).card := by
    have h1 : (T.image (fun x => x % p)).card ≤ T.card := Finset.card_image_le
    rw [Finset.card_range]; omega
  obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.2 ⟨hsub, by intro hE; rw [hE] at hc; omega⟩)
  exact ⟨y, Finset.mem_range.1 hy1, fun x hx hxy => hy2 (Finset.mem_image.2 ⟨x, hx, hxy⟩)⟩

/-- **The floor.**  Three integers inside a window of width 5 always meet every class
modulo 2 or every class modulo 3. -/
theorem width_five_card_le_two (T : Finset ℕ) (lo : ℕ)
    (hw : ∀ x ∈ T, lo ≤ x ∧ x ≤ lo + 5) (hadm : Adm T) : T.card ≤ 2 := by
  obtain ⟨s, hs2, hs⟩ := hadm 2 Nat.prime_two
  obtain ⟨r, hr3, hr⟩ := hadm 3 Nat.prime_three
  have hinj : Set.InjOn (fun x => x % 6) (T : Set ℕ) := by
    intro x hx y hy h
    obtain ⟨hx1, hx2⟩ := hw x (by simpa using hx)
    obtain ⟨hy1, hy2⟩ := hw y (by simpa using hy)
    simp only at h
    omega
  have himg : T.image (fun x => x % 6) ⊆
      (Finset.range 6).filter (fun c => c % 2 ≠ s ∧ c % 3 ≠ r) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    have h2 := hs x hx
    have h3 := hr x hx
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_, ?_⟩ <;> omega
  have hcard : ((Finset.range 6).filter (fun c => c % 2 ≠ s ∧ c % 3 ≠ r)).card ≤ 2 := by
    interval_cases s <;> interval_cases r <;> decide
  calc T.card = (T.image (fun x => x % 6)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card himg
    _ ≤ 2 := hcard

theorem adm_026 : Adm ({0, 2, 6} : Finset ℕ) := by
  intro p hp
  have h2 := hp.two_le
  by_cases h4 : 4 ≤ p
  · exact omit_of_card_lt _ p hp.pos (by rw [show ({0,2,6} : Finset ℕ).card = 3 from by decide]; omega)
  · interval_cases p
    · exact ⟨1, by norm_num, by decide⟩
    · exact ⟨1, by norm_num, by decide⟩

theorem adm_02 : Adm ({0, 2} : Finset ℕ) := by
  intro p hp
  have h2 := hp.two_le
  by_cases h3 : 3 ≤ p
  · exact omit_of_card_lt _ p hp.pos (by rw [show ({0,2} : Finset ℕ).card = 2 from by decide]; omega)
  · interval_cases p
    · exact ⟨1, by norm_num, by decide⟩

theorem not_adm_024 : ¬ Adm ({0, 2, 4} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr, hall⟩ := h 3 Nat.prime_three
  interval_cases r
  · exact hall 0 (by decide) (by decide)
  · exact hall 4 (by decide) (by decide)
  · exact hall 2 (by decide) (by decide)

theorem proof :
    (∀ (T : Finset ℕ) (lo : ℕ), (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + 5) →
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) → T.card ≤ 2)
    ∧ (∀ (T : Finset ℕ) (lo d : ℕ), (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) → 3 ≤ T.card →
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) → 6 ≤ d)
    ∧ (({0, 2, 6} : Finset ℕ).card = 3 ∧
        ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6} : Finset ℕ), x % p ≠ r)
    ∧ (({0, 2} : Finset ℕ).card = 2 ∧
        ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2} : Finset ℕ), x % p ≠ r)
    ∧ ¬ (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 4} : Finset ℕ), x % p ≠ r) := by
  refine ⟨fun T lo hw hadm => width_five_card_le_two T lo hw hadm, ?_,
    ⟨by decide, adm_026⟩, ⟨by decide, adm_02⟩, not_adm_024⟩
  intro T lo d hw h3 hadm
  by_contra hd
  have : T.card ≤ 2 :=
    width_five_card_le_two T lo (fun x hx => by have := hw x hx; omega) hadm
  omega

end Submissions.AdmissibleTupleFloorSix.Floor
