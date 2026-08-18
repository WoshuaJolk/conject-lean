import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 10000

namespace Submissions.DHLTwoIsPolignac.Polignac

/-- Admissibility, with the load-bearing `r < p`. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- `DHL[k,2]`, uniform over admissible `k`-tuples, as in the Maynard–Tao / Polymath8b
literature. -/
def DHL2 (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → Admissible H →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 2 ≤ (H.filter (fun h => Nat.Prime (n + h))).card

/-- The `k = 2` endpoint of the Maynard–Tao reduction is de Polignac's conjecture, not the
twin prime conjecture.

An admissible pair is exactly an even-difference pair, so `DHL[2,2]` — which is uniform over
*all* admissible 2-tuples — says that **every** even gap occurs infinitely often.  That is de
Polignac, strictly more than twin primes, which is only its `h = 2` instance.  So the route
`DHL[k,2]` + narrow tuple cannot deliver `H₁ = 2` without delivering every even gap as well:
its `k = 2` endpoint overshoots the target. -/
theorem proof :
    (∀ a b : ℕ, a < b → (Admissible ({a, b} : Finset ℕ) ↔ Even (b - a)))
    ∧ (DHL2 2 ↔ ∀ h : ℕ, 0 < h → Even h →
        ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime n ∧ Nat.Prime (n + h))
    ∧ (DHL2 2 → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    ∧ (DHL2 2 → (∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 4))
              ∧ (∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 6)))
    ∧ (Admissible ({0, 2} : Finset ℕ) ∧ ¬ Admissible ({0, 3} : Finset ℕ)) := by
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
  -- (i) admissible pairs are exactly the even-difference pairs
  have pair : ∀ a b : ℕ, a < b → (Admissible ({a, b} : Finset ℕ) ↔ Even (b - a)) := by
    intro a b hab
    have hcard : ({a, b} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    constructor
    · intro hA
      obtain ⟨r, hr, hall⟩ := hA 2 Nat.prime_two
      have ha := hall a (by simp)
      have hb := hall b (by simp)
      exact ⟨(b - a) / 2, by omega⟩
    · rintro ⟨t, ht⟩ p hp
      by_cases hle : p ≤ 2
      · interval_cases p
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
        · refine ⟨1 - a % 2, by omega, ?_⟩
          intro h hh
          simp only [Finset.mem_insert, Finset.mem_singleton] at hh
          rcases hh with rfl | rfl <;> omega
      · exact big_prime _ p (by rw [hcard]; omega)
  have adm02 : Admissible ({0, 2} : Finset ℕ) := (pair 0 2 (by omega)).mpr ⟨1, by omega⟩
  have nadm03 : ¬ Admissible ({0, 3} : Finset ℕ) := by
    intro hA
    obtain ⟨t, ht⟩ := (pair 0 3 (by omega)).mp hA
    omega
  -- (ii) DHL[2,2] is de Polignac
  have main : DHL2 2 ↔ ∀ h : ℕ, 0 < h → Even h →
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime n ∧ Nat.Prime (n + h) := by
    constructor
    · intro hD h hh he N
      have hcard : ({0, h} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hadm : Admissible ({0, h} : Finset ℕ) := (pair 0 h hh).mpr (by simpa using he)
      obtain ⟨n, hn, hc⟩ := hD ({0, h} : Finset ℕ) hcard hadm N
      have heq : ({0, h} : Finset ℕ).filter (fun x => Nat.Prime (n + x)) = ({0, h} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard]; omega)
      have h0 : (0 : ℕ) ∈ ({0, h} : Finset ℕ).filter (fun x => Nat.Prime (n + x)) := by
        rw [heq]; simp
      have hh' : h ∈ ({0, h} : Finset ℕ).filter (fun x => Nat.Prime (n + x)) := by
        rw [heq]; simp
      exact ⟨n, hn, by simpa using (Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp hh').2⟩
    · intro hP H hcard hadm N
      have key : ∀ a b : ℕ, a < b → Admissible ({a, b} : Finset ℕ) →
          ∃ n : ℕ, N < n ∧
            2 ≤ (({a, b} : Finset ℕ).filter (fun x => Nat.Prime (n + x))).card := by
        intro a b hab hadm'
        have hcard' : ({a, b} : Finset ℕ).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        obtain ⟨q, hq, hq1, hq2⟩ := hP (b - a) (by omega) ((pair a b hab).mp hadm') (N + a)
        refine ⟨q - a, by omega, ?_⟩
        have e1 : q - a + a = q := by omega
        have e2 : q - a + b = q + (b - a) := by omega
        have hsub : ({a, b} : Finset ℕ) ⊆
            ({a, b} : Finset ℕ).filter (fun x => Nat.Prime (q - a + x)) := by
          intro x hx
          rw [Finset.mem_filter]
          refine ⟨hx, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · rw [e1]; exact hq1
          · rw [e2]; exact hq2
        have hle := Finset.card_le_card hsub
        omega
      obtain ⟨a, b, hne, rfl⟩ := Finset.card_eq_two.mp hcard
      rcases Nat.lt_or_ge a b with hab | hab
      · exact key a b hab hadm
      · have hba : b < a := by omega
        rw [Finset.pair_comm a b] at hadm ⊢
        exact key b a hba hadm
  refine ⟨pair, main, ?_, ?_, adm02, nadm03⟩
  · intro hD N
    obtain ⟨n, hn, h1, h2⟩ := main.mp hD 2 (by omega) ⟨1, by omega⟩ N
    exact ⟨n, hn, h1, h2⟩
  · refine fun hD => ⟨fun N => ?_, fun N => ?_⟩
    · obtain ⟨n, hn, h1, h2⟩ := main.mp hD 4 (by omega) ⟨2, by omega⟩ N
      exact ⟨n, hn, h1, h2⟩
    · obtain ⟨n, hn, h1, h2⟩ := main.mp hD 6 (by omega) ⟨3, by omega⟩ N
      exact ⟨n, hn, h1, h2⟩

end Submissions.DHLTwoIsPolignac.Polignac
