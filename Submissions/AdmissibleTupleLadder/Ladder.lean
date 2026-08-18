import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace Submissions.AdmissibleTupleLadder.Ladder

def Adm (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r

theorem Adm.mono {S T : Finset ℕ} (h : S ⊆ T) (hT : Adm T) : Adm S := by
  intro p hp
  obtain ⟨r, hr, hall⟩ := hT p hp
  exact ⟨r, hr, fun x hx => hall x (h hx)⟩

/-- Three integers inside a window of width 5 meet every class mod 2 or every class mod 3. -/
theorem width_five (T : Finset ℕ) (lo : ℕ)
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

/-- The ladder: `f k` is the least diameter that `k` points can have. -/
def f (k : ℕ) : ℕ := 6 * ((k - 1) / 2) + 2 * ((k - 1) % 2)

theorem f_mono {a b : ℕ} (h : a ≤ b) : f a ≤ f b := by unfold f; omega

theorem f_step {k : ℕ} (h : 3 ≤ k) : f k = f (k - 2) + 6 := by unfold f; omega

theorem two_apart (T : Finset ℕ) (lo d : ℕ) (h2 : 2 ≤ T.card)
    (hw : ∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) (hadm : Adm T) : 2 ≤ d := by
  obtain ⟨s, hs2, hs⟩ := hadm 2 Nat.prime_two
  obtain ⟨a, ha', b, hb', hab⟩ := Finset.one_lt_card.1 h2
  have ha := hw a ha'
  have hb := hw b hb'
  have hsa := hs a ha'
  have hsb := hs b hb'
  omega

theorem ladder : ∀ k : ℕ, ∀ (T : Finset ℕ) (lo d : ℕ), T.card = k →
    (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) → Adm T → f k ≤ d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T lo d hcard hw hadm
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · simp [f]
      · simp [f]
      · exact le_trans (by simp [f]) (two_apart T lo d (by omega) hw hadm)
    · -- k ≥ 3
      have hne : T.Nonempty := Finset.card_pos.1 (by omega)
      set m := T.max' hne with hm
      have hmT : m ∈ T := T.max'_mem hne
      have hmle : ∀ x ∈ T, x ≤ m := fun x hx => T.le_max' x hx
      -- the top window [m-5, m] holds at most two elements
      have htop : (T.filter (fun x => ¬ (x + 6 ≤ m))).card ≤ 2 := by
        refine width_five _ (m - 5) ?_ (Adm.mono (Finset.filter_subset _ _) hadm)
        intro x hx
        obtain ⟨hxT, hxc⟩ := Finset.mem_filter.1 hx
        have := hmle x hxT
        simp only [not_le] at hxc
        omega
      have hsplit : T.card ≤ (T.filter (fun x => x + 6 ≤ m)).card
          + (T.filter (fun x => ¬ (x + 6 ≤ m))).card := by
        rw [Finset.card_filter_add_card_filter_not (fun x => x + 6 ≤ m)]
      have hlow : k - 2 ≤ (T.filter (fun x => x + 6 ≤ m)).card := by omega
      -- m is at least lo + 6, since T does not fit in a window of width 5
      have hm6 : lo + 6 ≤ m := by
        by_contra hc
        have : T.card ≤ 2 := by
          refine width_five T lo (fun x hx => ?_) hadm
          have := hw x hx; have := hmle x hx; omega
        omega
      have hsub := ih (T.filter (fun x => x + 6 ≤ m)).card ?_
        (T.filter (fun x => x + 6 ≤ m)) lo (m - 6 - lo) rfl ?_
        (Adm.mono (Finset.filter_subset _ _) hadm)
      · have hmd : m ≤ lo + d := (hw m hmT).2
        have : f (k - 2) ≤ f (T.filter (fun x => x + 6 ≤ m)).card := f_mono hlow
        rw [f_step hk]
        omega
      · have : (T.filter (fun x => x + 6 ≤ m)).card ≤ T.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have hnm : ¬ (m + 6 ≤ m) := by omega
        have : m ∉ T.filter (fun x => x + 6 ≤ m) := by
          simp only [Finset.mem_filter]; tauto
        have hss : T.filter (fun x => x + 6 ≤ m) ⊂ T :=
          Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨m, hmT, this⟩
        have := Finset.card_lt_card hss
        omega
      · intro x hx
        obtain ⟨hxT, hxc⟩ := Finset.mem_filter.1 hx
        have := (hw x hxT).1
        omega


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

/-- Admissibility from a finite check at the primes up to `card`, plus pigeonhole above. -/
theorem adm_of_small (T : Finset ℕ) (n : ℕ) (hcard : T.card = n)
    (hsmall : ∀ q ∈ Finset.Ico 2 (n + 1), ∃ r ∈ Finset.range q, ∀ x ∈ T, x % q ≠ r) :
    Adm T := by
  intro p hp
  by_cases hle : p ≤ n
  · obtain ⟨r, hr, hall⟩ := hsmall p (Finset.mem_Ico.2 ⟨hp.two_le, by omega⟩)
    exact ⟨r, Finset.mem_range.1 hr, hall⟩
  · exact omit_of_card_lt T p hp.pos (by omega)

theorem adm2 : Adm ({0, 2} : Finset ℕ) := adm_of_small _ 2 (by decide) (by decide)
theorem adm3 : Adm ({0, 2, 6} : Finset ℕ) := adm_of_small _ 3 (by decide) (by decide)
theorem adm4 : Adm ({0, 2, 6, 8} : Finset ℕ) := adm_of_small _ 4 (by decide) (by decide)
theorem adm5 : Adm ({0, 2, 6, 8, 12} : Finset ℕ) := adm_of_small _ 5 (by decide) (by decide)

theorem not_adm_024 : ¬ Adm ({0, 2, 4} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr, hall⟩ := h 3 Nat.prime_three
  interval_cases r
  · exact hall 0 (by decide) (by decide)
  · exact hall 4 (by decide) (by decide)
  · exact hall 2 (by decide) (by decide)

theorem proof :
    (∀ (T : Finset ℕ) (lo d : ℕ), (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) →
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) →
        6 * ((T.card - 1) / 2) + 2 * ((T.card - 1) % 2) ≤ d)
    ∧ (∀ (T : Finset ℕ) (lo d : ℕ), T.card = 50 → (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) →
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) → 146 ≤ d)
    ∧ (({0, 2} : Finset ℕ).card = 2 ∧ (∀ x ∈ ({0, 2} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 2) ∧
        ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2} : Finset ℕ), x % p ≠ r)
    ∧ (({0, 2, 6} : Finset ℕ).card = 3 ∧ (∀ x ∈ ({0, 2, 6} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 6) ∧
        ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6} : Finset ℕ), x % p ≠ r)
    ∧ (({0, 2, 6, 8} : Finset ℕ).card = 4 ∧
        (∀ x ∈ ({0, 2, 6, 8} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 8) ∧
        ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6, 8} : Finset ℕ), x % p ≠ r)
    ∧ (({0, 2, 6, 8, 12} : Finset ℕ).card = 5 ∧
        (∀ x ∈ ({0, 2, 6, 8, 12} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 12) ∧
        ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6, 8, 12} : Finset ℕ), x % p ≠ r)
    ∧ ¬ (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 4} : Finset ℕ), x % p ≠ r) := by
  refine ⟨fun T lo d hw hadm => ladder T.card T lo d rfl hw hadm, ?_,
    ⟨by decide, by decide, adm2⟩, ⟨by decide, by decide, adm3⟩,
    ⟨by decide, by decide, adm4⟩, ⟨by decide, by decide, adm5⟩, not_adm_024⟩
  intro T lo d hc hw hadm
  have h := ladder T.card T lo d rfl hw hadm
  rw [hc] at h
  have hf : f 50 = 146 := by unfold f; norm_num
  omega

end Submissions.AdmissibleTupleLadder.Ladder
