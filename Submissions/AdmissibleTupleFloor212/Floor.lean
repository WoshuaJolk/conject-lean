import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000

namespace Submissions.AdmissibleTupleFloor212.Floor

/-- A finite set of shifts is *admissible* when for every prime `p` some residue class
`r < p` mod `p` contains no element of it.  The bound `r < p` is load-bearing. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- A quantitative floor under every narrow-admissible-tuple search, and the method ceiling
it forces on the `k = 50` Maynard–Tao / Polymath8b route.

The counting is one injection.  Admissibility at `2, 3, 5, 7` names four omitted classes
`r₂, r₃, r₅, r₇`; by CRT exactly `1·2·4·6 = 48` of the `210` residues mod `210` survive all
four, whatever the four classes are — a fact discharged here by `decide` over all
`2·3·5·7 = 210` choices, with no `native_decide`.  Every `h ∈ H` therefore has `h % 210` in a
fixed `48`-element set `T`, and `h ↦ (h / 210, h % 210)` is injective, so
`H.card ≤ 48 · (d / 210 + 1)` whenever `H ⊆ [0, d]`.

At `d < 210` the right-hand side is `48`, so no admissible tuple of diameter below `210` has
more than `48` elements: `H(50) ≥ 210`.  Since `DHL[k,2]` plus an admissible `k`-tuple of
diameter `d` is what yields `H₁ ≤ d`, the `k = 50` route provably cannot output any bound
below `210`, and any bound below `210` by this route requires `DHL[k,2]` for some `k ≤ 48` —
strictly stronger analytic input than Polymath8b's. -/
theorem proof :
    (∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) →
        H.card ≤ 48 * (d / 210 + 1))
    ∧ (∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) → d ≤ 211 → H.card ≤ 49)
    ∧ (∀ (H : Finset ℕ) (d : ℕ), Admissible H → H.card = 50 → (∀ h ∈ H, h ≤ d) → 212 ≤ d)
    ∧ (∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) → 2 * (H.card - 1) ≤ d)
    ∧ (Admissible ({0, 2} : Finset ℕ) ∧ ({0, 2} : Finset ℕ).card = 2
        ∧ ¬ Admissible ({0, 2, 4} : Finset ℕ)) := by
  have tcard : ∀ r2 r3 r5 r7 : ℕ, r2 < 2 → r3 < 3 → r5 < 5 → r7 < 7 →
      ((Finset.range 210).filter
        (fun x => x % 2 ≠ r2 ∧ x % 3 ≠ r3 ∧ x % 5 ≠ r5 ∧ x % 7 ≠ r7)).card = 48 := by
    intro r2 r3 r5 r7 h2 h3 h5 h7
    interval_cases r2 <;> interval_cases r3 <;> interval_cases r5 <;> interval_cases r7 <;>
      decide
  have tcard212 : ∀ r2 r3 r5 r7 : ℕ, r2 < 2 → r3 < 3 → r5 < 5 → r7 < 7 →
      ((Finset.range 212).filter
        (fun x => x % 2 ≠ r2 ∧ x % 3 ≠ r3 ∧ x % 5 ≠ r5 ∧ x % 7 ≠ r7)).card ≤ 49 := by
    intro r2 r3 r5 r7 h2 h3 h5 h7
    interval_cases r2 <;> interval_cases r3 <;> interval_cases r5 <;> interval_cases r7 <;>
      decide
  have sharp : ∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) → d ≤ 211 →
      H.card ≤ 49 := by
    intro H d hadm hd hdlt
    obtain ⟨r2, hr2, h2⟩ := hadm 2 Nat.prime_two
    obtain ⟨r3, hr3, h3⟩ := hadm 3 Nat.prime_three
    obtain ⟨r5, hr5, h5⟩ := hadm 5 (by decide)
    obtain ⟨r7, hr7, h7⟩ := hadm 7 (by decide)
    have hsub : H ⊆ (Finset.range 212).filter
        (fun x => x % 2 ≠ r2 ∧ x % 3 ≠ r3 ∧ x % 5 ≠ r5 ∧ x % 7 ≠ r7) := by
      intro h hh
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := hd h hh; omega, h2 h hh, h3 h hh, h5 h hh, h7 h hh⟩
    exact le_trans (Finset.card_le_card hsub) (tcard212 r2 r3 r5 r7 hr2 hr3 hr5 hr7)
  have main : ∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) →
      H.card ≤ 48 * (d / 210 + 1) := by
    intro H d hadm hd
    obtain ⟨r2, hr2, h2⟩ := hadm 2 Nat.prime_two
    obtain ⟨r3, hr3, h3⟩ := hadm 3 Nat.prime_three
    obtain ⟨r5, hr5, h5⟩ := hadm 5 (by decide)
    obtain ⟨r7, hr7, h7⟩ := hadm 7 (by decide)
    set T : Finset ℕ := (Finset.range 210).filter
      (fun x => x % 2 ≠ r2 ∧ x % 3 ≠ r3 ∧ x % 5 ≠ r5 ∧ x % 7 ≠ r7) with hT
    have hTc : T.card = 48 := by rw [hT]; exact tcard r2 r3 r5 r7 hr2 hr3 hr5 hr7
    have hinj : Set.InjOn (fun h => (h / 210, h % 210)) (H : Set ℕ) := by
      intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      omega
    have hmaps : ∀ h ∈ H, (h / 210, h % 210) ∈ (Finset.range (d / 210 + 1)) ×ˢ T := by
      intro h hh
      rw [Finset.mem_product]
      refine ⟨Finset.mem_range.mpr (by have := hd h hh; omega), ?_⟩
      rw [hT, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · have := h2 h hh; omega
      · have := h3 h hh; omega
      · have := h5 h hh; omega
      · have := h7 h hh; omega
    have hc := Finset.card_le_card_of_injOn (fun h => (h / 210, h % 210)) hmaps hinj
    rw [Finset.card_product, Finset.card_range, hTc] at hc
    omega
  have parity : ∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) →
      2 * (H.card - 1) ≤ d := by
    intro H d hadm hd
    obtain ⟨r2, hr2, h2⟩ := hadm 2 Nat.prime_two
    have hinj : Set.InjOn (fun h => h / 2) (H : Set ℕ) := by
      intro a ha b hb hab
      simp only at hab
      have := h2 a ha
      have := h2 b hb
      omega
    have hmaps : ∀ h ∈ H, h / 2 ∈ Finset.range (d / 2 + 1) := by
      intro h hh
      exact Finset.mem_range.mpr (by have := hd h hh; omega)
    have hc := Finset.card_le_card_of_injOn (fun h => h / 2) hmaps hinj
    rw [Finset.card_range] at hc
    omega
  have big_prime : ∀ (H : Finset ℕ) (p : ℕ), H.card < p → ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
    intro H p hp
    by_contra hc
    push Not at hc
    have hsub : Finset.range p ⊆ H.image (fun h => h % p) := by
      intro r hr
      rw [Finset.mem_range] at hr
      obtain ⟨h, hh, hhr⟩ := hc r hr
      exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 := Finset.card_image_le (s := H) (f := fun h => h % p)
    omega
  have card02 : ({0, 2} : Finset ℕ).card = 2 := by decide
  have adm02 : Admissible ({0, 2} : Finset ℕ) := by
    intro p hp
    by_cases hle : p ≤ 2
    · interval_cases p <;> revert hp <;> decide
    · exact big_prime _ p (by rw [card02]; omega)
  have nadm024 : ¬ Admissible ({0, 2, 4} : Finset ℕ) := by
    intro hA
    exact absurd (hA 3 (by decide)) (by decide)
  refine ⟨main, sharp, ?_, parity, ⟨adm02, card02, nadm024⟩⟩
  intro H d hadm hcard hd
  by_contra hcon
  have := sharp H d hadm hd (by omega)
  omega

end Submissions.AdmissibleTupleFloor212.Floor
