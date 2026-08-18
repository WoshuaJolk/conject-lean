import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push

set_option maxRecDepth 100000

namespace Submissions.TwinPrimesDHLReduction.Reduction

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁` as an element of `ℕ∞`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- A finite set of shifts is *admissible* when for every prime `p` some residue class
`r < p` mod `p` contains no element of it.  The bound `r < p` is load-bearing: without it
`r := p` satisfies the clause for every set. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- `DHL[k,2]`: for every admissible `k`-tuple `H` and every bound `N` there is `n > N` such
that at least two of the shifts `n + h`, `h ∈ H`, are prime. -/
def DHL2 (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → Admissible H →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 2 ≤ (H.filter (fun h => Nat.Prime (n + h))).card

/-- An admissible 50-tuple of diameter exactly 246, found by beam search over the deleted
residue vector `(r_2, …, r_47)` and re-verified independently. -/
def tuple50 : Finset ℕ :=
  ([0, 2, 6, 8, 12, 18, 20, 26, 32, 36, 42, 48, 50, 56, 62, 68, 72, 78, 86, 90, 96, 98,
    102, 110, 116, 120, 128, 132, 138, 140, 146, 152, 156, 158, 162, 176, 180, 182, 186,
    188, 198, 200, 210, 212, 216, 218, 230, 240, 242, 246] : List ℕ).toFinset

/-- `DHL[k,2]` plus an admissible `k`-tuple inside `[0, d]` forces `H₁ ≤ d`; the explicit
admissible 50-tuple of diameter 246 is checked by the kernel; hence `DHL[50,2] → H₁ ≤ 246`
and `DHL[2,2] →` the twin prime conjecture.

The reduction is the Maynard–Tao pigeonhole made precise.  `DHL[k,2]` hands back, beyond
every bound, an `n` and two distinct shifts `x < y` in `H` with `n + x` and `n + y` prime.
Those two primes are at distance `y - x ≤ d`, so the *consecutive* prime immediately after
`n + x` is at most `n + y`: writing `i = count Nat.Prime (n + x)`, `Nat.nth_count` gives
`nth i = n + x`, `count_succ` gives `count (n + x + 1) = i + 1`, monotonicity of `count`
gives `i + 1 ≤ count (n + y)`, and monotonicity of `nth` then gives `nth (i + 1) ≤ n + y`.
So `gap i ≤ d`, and `i ≥ M` because `n` was chosen past `nth M`.  Frequently-small gaps
give `liminf ≤ d`.

Admissibility of the 50-tuple splits at `p = 50`: primes below are a single kernel `decide`
(no `native_decide`), primes above are pigeonhole, since the image of a 50-element set under
`(· % p)` cannot exhaust `Finset.range p` when `p > 50`. -/
theorem proof :
    (Admissible ({0, 2} : Finset ℕ) ∧ ¬ Admissible ({0, 2, 4} : Finset ℕ) ∧ ¬ DHL2 1)
    ∧ (∀ (H : Finset ℕ) (p : ℕ), H.card < p → ∃ r < p, ∀ h ∈ H, h % p ≠ r)
    ∧ (∀ (d : ℕ) (H : Finset ℕ), DHL2 H.card → Admissible H → (∀ h ∈ H, h ≤ d) →
        H1 ≤ (d : ℕ∞))
    ∧ (tuple50.card = 50 ∧ 0 ∈ tuple50 ∧ 246 ∈ tuple50 ∧ (∀ h ∈ tuple50, h ≤ 246)
        ∧ Admissible tuple50)
    ∧ (DHL2 50 → H1 ≤ (246 : ℕ∞))
    ∧ (DHL2 2 → H1 ≤ (2 : ℕ∞))
    ∧ (DHL2 2 → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
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
  have card50 : tuple50.card = 50 := by decide
  have adm50 : Admissible tuple50 := by
    intro p hp
    by_cases hle : p ≤ 50
    · interval_cases p <;> revert hp <;> decide
    · exact big_prime tuple50 p (by rw [card50]; omega)
  have card02 : ({0, 2} : Finset ℕ).card = 2 := by decide
  have adm02 : Admissible ({0, 2} : Finset ℕ) := by
    intro p hp
    by_cases hle : p ≤ 2
    · interval_cases p <;> revert hp <;> decide
    · exact big_prime _ p (by rw [card02]; omega)
  have nadm024 : ¬ Admissible ({0, 2, 4} : Finset ℕ) := by
    intro hA
    exact absurd (hA 3 (by decide)) (by decide)
  have card0 : ({0} : Finset ℕ).card = 1 := by decide
  have adm0 : Admissible ({0} : Finset ℕ) := by
    intro p hp
    by_cases hle : p ≤ 1
    · interval_cases p <;> revert hp <;> decide
    · exact big_prime _ p (by rw [card0]; omega)
  have ndhl1 : ¬ DHL2 1 := by
    intro h
    obtain ⟨n, -, hcard⟩ := h ({0} : Finset ℕ) card0 adm0 0
    have := Finset.card_le_card (Finset.filter_subset (fun h => Nat.Prime (n + h))
      ({0} : Finset ℕ))
    rw [card0] at this
    omega
  have reduction : ∀ (d : ℕ) (H : Finset ℕ), DHL2 H.card → Admissible H →
      (∀ h ∈ H, h ≤ d) → H1 ≤ (d : ℕ∞) := by
    intro d H hdhl hadm hd
    have hinf : {p | Nat.Prime p}.Infinite := Nat.infinite_setOfPred_prime
    have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono hinf
    have hfr : ∃ᶠ i in Filter.atTop, (gap i : ℕ∞) ≤ (d : ℕ∞) := by
      rw [Filter.frequently_atTop]
      intro M
      obtain ⟨n, hn, hcard⟩ := hdhl H rfl hadm (Nat.nth Nat.Prime M)
      obtain ⟨a, ha, b, hb, hab⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (H.filter (fun h => Nat.Prime (n + h))).card)
      have key : ∀ x y : ℕ, y ∈ H → x < y → Nat.Prime (n + x) → Nat.Prime (n + y) →
          ∃ i, M ≤ i ∧ (gap i : ℕ∞) ≤ (d : ℕ∞) := by
        intro x y hy hxy hpx hpy
        have hq1big : Nat.nth Nat.Prime M < n + x := by omega
        have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime (n + x)) = n + x := Nat.nth_count hpx
        have hMi : M ≤ Nat.count Nat.Prime (n + x) := by
          have h' : Nat.nth Nat.Prime M < Nat.nth Nat.Prime (Nat.count Nat.Prime (n + x)) := by
            rw [hnth]; exact hq1big
          exact le_of_lt ((Nat.nth_lt_nth hinf).mp h')
        have hcs : Nat.count Nat.Prime (n + x + 1) = Nat.count Nat.Prime (n + x) + 1 := by
          rw [Nat.count_succ]; simp [hpx]
        have hle : Nat.count Nat.Prime (n + x) + 1 ≤ Nat.count Nat.Prime (n + y) := by
          rw [← hcs]; exact Nat.count_monotone Nat.Prime (by omega)
        have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime (n + x) + 1) ≤ n + y := by
          have h3 := hmono.monotone hle
          rwa [Nat.nth_count hpy] at h3
        refine ⟨Nat.count Nat.Prime (n + x), hMi, ?_⟩
        have hyd : y ≤ d := hd y hy
        have hgle : gap (Nat.count Nat.Prime (n + x)) ≤ d := by
          unfold gap; rw [hnth]; omega
        exact_mod_cast hgle
      obtain ⟨haH, hpa⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbH, hpb⟩ := Finset.mem_filter.mp hb
      rcases lt_or_gt_of_ne hab with h | h
      · exact key a b hbH h hpa hpb
      · exact key b a haH h hpb hpa
    exact Filter.liminf_le_of_frequently_le' hfr
  refine ⟨⟨adm02, nadm024, ndhl1⟩, big_prime, reduction, ⟨card50, by decide, by decide, by decide,
    adm50⟩, ?_, ?_, ?_⟩
  · exact fun h => reduction 246 tuple50 (by rw [card50]; exact h) adm50 (by decide)
  · exact fun h => reduction 2 ({0, 2} : Finset ℕ) (by rw [card02]; exact h) adm02 (by decide)
  · intro h N
    obtain ⟨n, hn, hcard⟩ := h ({0, 2} : Finset ℕ) card02 adm02 N
    have heq : ({0, 2} : Finset ℕ).filter (fun h => Nat.Prime (n + h)) = ({0, 2} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [card02]; omega)
    have h0 : (0 : ℕ) ∈ ({0, 2} : Finset ℕ).filter (fun h => Nat.Prime (n + h)) := by
      rw [heq]; decide
    have h2 : (2 : ℕ) ∈ ({0, 2} : Finset ℕ).filter (fun h => Nat.Prime (n + h)) := by
      rw [heq]; decide
    refine ⟨n, hn, ?_, ?_⟩
    · simpa using (Finset.mem_filter.mp h0).2
    · simpa using (Finset.mem_filter.mp h2).2

end Submissions.TwinPrimesDHLReduction.Reduction
