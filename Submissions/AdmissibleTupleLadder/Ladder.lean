import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
Witness for `Statements.AdmissibleTupleLadder.statement`.

**The mechanism.**  Admissibility at `p = 2` puts all of `T` in one class mod 2; at `p = 3`
it leaves only two of the three classes mod 3.  So any *three* distinct elements have two
agreeing mod 3, and those two also agree mod 2, hence agree mod 6 and differ by at least 6.
Applied to the three largest elements this says: deleting the top two elements of `T` costs
at least 6 of the diameter.  Strong induction in steps of two then gives the ladder, with
`k ≤ 1` and `k = 2` as the base cases (`k = 2` uses only the mod-2 fact).

No sorted enumeration is needed: the induction deletes `max'` twice and recurses.
-/

namespace Submissions.AdmissibleTupleLadder.Ladder

/-- The two consequences of admissibility that the ladder actually uses.  Both are inherited
by subsets, which is what makes the induction go through. -/
def P (T : Finset ℕ) : Prop :=
  (∀ x ∈ T, ∀ y ∈ T, x % 2 = y % 2) ∧ (∃ r3 : ℕ, r3 < 3 ∧ ∀ x ∈ T, x % 3 ≠ r3)

private lemma P_mono {S T : Finset ℕ} (hst : S ⊆ T) (h : P T) : P S := by
  obtain ⟨h2, r3, hr3, h3⟩ := h
  exact ⟨fun x hx y hy => h2 x (hst hx) y (hst hy), r3, hr3, fun x hx => h3 x (hst hx)⟩

private lemma P_of_admissible {T : Finset ℕ}
    (h : ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) : P T := by
  obtain ⟨r2, hr2, h2⟩ := h 2 Nat.prime_two
  obtain ⟨r3, hr3, h3⟩ := h 3 Nat.prime_three
  refine ⟨fun x hx y hy => ?_, r3, hr3, h3⟩
  have hx2 := h2 x hx
  have hy2 := h2 y hy
  interval_cases r2 <;> omega

/-- Two distinct elements of `T` differ by at least 2. -/
private lemma two_of_two {T : Finset ℕ} (hP : P T) {x y : ℕ}
    (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y) : 2 ≤ y - x := by
  have := hP.1 x hx y hy
  omega

/-- Two naturals agreeing mod 2 and mod 3 agree mod 6, so a strict pair differs by ≥ 6. -/
private lemma six_of_pair {u v : ℕ} (h2 : u % 2 = v % 2) (h3 : u % 3 = v % 3) (h : u < v) :
    6 ≤ v - u := by
  have d2 : 2 ∣ (v - u) := by omega
  have d3 : 3 ∣ (v - u) := by omega
  have d6 : 2 * 3 ∣ (v - u) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d2 d3
  exact Nat.le_of_dvd (by omega) (by simpa using d6)

/-- Three distinct elements of `T` span at least 6: two of them agree mod 3, and everything
in `T` agrees mod 2, so those two agree mod 6. -/
private lemma six_of_three {T : Finset ℕ} (hP : P T) {x y z : ℕ}
    (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) (hxy : x < y) (hyz : y < z) : 6 ≤ z - x := by
  obtain ⟨h2, r3, hr3, h3⟩ := hP
  have e1 := h2 x hx y hy
  have e2 := h2 y hy z hz
  have e3 := h2 x hx z hz
  have n1 := h3 x hx
  have n2 := h3 y hy
  have n3 := h3 z hz
  have hdisj : x % 3 = y % 3 ∨ y % 3 = z % 3 ∨ x % 3 = z % 3 := by
    interval_cases r3 <;> omega
  rcases hdisj with h | h | h
  · have := six_of_pair e1 h hxy; omega
  · have := six_of_pair e2 h hyz; omega
  · exact six_of_pair e3 h (by omega)

/-- The ladder, by strong induction on the cardinality in steps of two. -/
private lemma ladder : ∀ k : ℕ, ∀ (T : Finset ℕ) (lo d : ℕ), T.card = k →
    (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) → P T →
    6 * ((k - 1) / 2) + 2 * ((k - 1) % 2) ≤ d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T lo d hcard hbd hP
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> simp
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · -- k = 2 : two distinct elements of the same parity
      have h2 : 2 = k := by omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
      rcases Nat.lt_or_ge x y with hlt | hge
      · have := two_of_two hP hx hy hlt
        have := (hbd x hx).1; have := (hbd y hy).2
        interval_cases k <;> omega
      · have hlt : y < x := lt_of_le_of_ne hge (Ne.symm hxy)
        have := two_of_two hP hy hx hlt
        have := (hbd y hy).1; have := (hbd x hx).2
        interval_cases k <;> omega
    · -- k ≥ 3 : delete the top two elements, losing at least 6 of the diameter
      have hne : T.Nonempty := by rw [← Finset.card_pos, hcard]; omega
      have ha : T.max' hne ∈ T := T.max'_mem hne
      set a := T.max' hne with hadef
      have hc1 : (T.erase a).card = k - 1 := by rw [Finset.card_erase_of_mem ha, hcard]
      have hne1 : (T.erase a).Nonempty := by rw [← Finset.card_pos, hc1]; omega
      have hb1 : (T.erase a).max' hne1 ∈ T.erase a := (T.erase a).max'_mem hne1
      set b := (T.erase a).max' hne1 with hbdef
      have hbT : b ∈ T := Finset.mem_of_mem_erase hb1
      have hc2 : ((T.erase a).erase b).card = k - 2 := by
        rw [Finset.card_erase_of_mem hb1, hc1]; omega
      have hne2 : ((T.erase a).erase b).Nonempty := by rw [← Finset.card_pos, hc2]; omega
      have hcc : ((T.erase a).erase b).max' hne2 ∈ (T.erase a).erase b :=
        ((T.erase a).erase b).max'_mem hne2
      set c := ((T.erase a).erase b).max' hne2 with hcdef
      have hcT1 : c ∈ T.erase a := Finset.mem_of_mem_erase hcc
      have hcT : c ∈ T := Finset.mem_of_mem_erase hcT1
      have hba : b < a := lt_of_le_of_ne (T.le_max' b hbT) (Finset.ne_of_mem_erase hb1)
      have hcb : c < b := lt_of_le_of_ne ((T.erase a).le_max' c hcT1)
        (Finset.ne_of_mem_erase hcc)
      have h6 : 6 ≤ a - c := six_of_three hP hcT hbT ha hcb hba
      have hsub : (T.erase a).erase b ⊆ T :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hbd2 : ∀ x ∈ (T.erase a).erase b, lo ≤ x ∧ x ≤ lo + (c - lo) := by
        intro x hx
        have h1 := (hbd x (hsub hx)).1
        have h2 : x ≤ c := ((T.erase a).erase b).le_max' x hx
        have h3 := (hbd c hcT).1
        omega
      have key := ih (k - 2) (by omega) ((T.erase a).erase b) lo (c - lo) hc2 hbd2
        (P_mono hsub hP)
      have hale := (hbd a ha).2
      have hclo := (hbd c hcT).1
      omega

/-- Pigeonhole: for `p` larger than `T.card`, admissibility at `p` is automatic. -/
private lemma admissible_of_small {T : Finset ℕ} {B : ℕ} (hcard : T.card < B)
    (hsmall : ∀ p : ℕ, p.Prime → p < B → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) :
    ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r := by
  intro p hp
  rcases Nat.lt_or_ge p B with h | h
  · exact hsmall p hp h
  · by_contra hcon
    push_neg at hcon
    have hsub : Finset.range p ⊆ T.image (fun x => x % p) := by
      intro r hr
      obtain ⟨x, hx, hxr⟩ := hcon r (Finset.mem_range.mp hr)
      exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 : (T.image (fun x => x % p)).card ≤ T.card := Finset.card_image_le
    omega

private lemma adm02 : ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2} : Finset ℕ), x % p ≠ r := by
  refine admissible_of_small (B := 3) (by decide) ?_
  intro p hp hpB
  have := hp.two_le
  interval_cases p
  · exact ⟨1, by norm_num, by decide⟩

private lemma adm026 : ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6} : Finset ℕ), x % p ≠ r := by
  refine admissible_of_small (B := 4) (by decide) ?_
  intro p hp hpB
  have := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; norm_num; done)
      | (refine ⟨1, ?_, ?_⟩ <;> decide)

private lemma adm0268 : ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6, 8} : Finset ℕ), x % p ≠ r := by
  refine admissible_of_small (B := 5) (by decide) ?_
  intro p hp hpB
  have := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; norm_num; done)
      | (refine ⟨1, ?_, ?_⟩ <;> decide)

private lemma adm026812 : ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6, 8, 12} : Finset ℕ), x % p ≠ r := by
  refine admissible_of_small (B := 6) (by decide) ?_
  intro p hp hpB
  have := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; norm_num; done)
      | (refine ⟨1, ?_, ?_⟩ <;> decide)
      | (refine ⟨4, ?_, ?_⟩ <;> decide)

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
  refine ⟨?_, ?_, ⟨by decide, by decide, adm02⟩, ⟨by decide, by decide, adm026⟩,
    ⟨by decide, by decide, adm0268⟩, ⟨by decide, by decide, adm026812⟩, ?_⟩
  · intro T lo d hbd hadm
    exact ladder T.card T lo d rfl hbd (P_of_admissible hadm)
  · intro T lo d hc hbd hadm
    have := ladder T.card T lo d rfl hbd (P_of_admissible hadm)
    rw [hc] at this
    omega
  · intro h
    obtain ⟨r, hr, h3⟩ := h 3 Nat.prime_three
    interval_cases r
    · exact absurd (h3 0 (by decide)) (by decide)
    · exact absurd (h3 4 (by decide)) (by decide)
    · exact absurd (h3 2 (by decide)) (by decide)

end Submissions.AdmissibleTupleLadder.Ladder
