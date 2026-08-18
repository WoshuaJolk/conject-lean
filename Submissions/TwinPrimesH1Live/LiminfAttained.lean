import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

namespace Submissions.TwinPrimesH1Live.LiminfAttained

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁` as an element of `ℕ∞`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- A finite `ℕ∞`-valued liminf of a `ℕ`-valued sequence is attained infinitely often; hence
a finite `H₁` is even, and any ceiling `H₁ ≤ B` confines `H₁` to an even value in `[2, B]`.

The one idea is that `ℕ` is discrete.  Write `L` for the liminf.  From `g - 1 < L` we get
`g - 1 < u n` eventually, i.e. `g ≤ u n` eventually; from `L < g + 1` we get `u n < g + 1`
frequently, i.e. `u n ≤ g` frequently.  Intersecting an eventual with a frequent gives
`u n = g` frequently — the step that fails for a real-valued sequence, where the liminf need
not be attained at all.  Everything after that is transport: the gap sequence is even and
`≥ 2` from index 1 on (two primes above `2` are both odd), and `∃ᶠ` meets `∀ᶠ`, so the value
`g` inherits both. -/
theorem proof :
    (∀ (u : ℕ → ℕ) (g : ℕ),
        Filter.liminf (fun n => (u n : ℕ∞)) Filter.atTop = (g : ℕ∞) →
        (∀ᶠ n in Filter.atTop, g ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = g))
    ∧ (∀ g : ℕ, H1 = (g : ℕ∞) →
        2 ≤ g ∧ Even g ∧ (∃ᶠ n in Filter.atTop, gap n = g))
    ∧ (∀ B : ℕ, H1 ≤ (B : ℕ∞) →
        ∃ g : ℕ, H1 = (g : ℕ∞) ∧ 2 ≤ g ∧ g ≤ B ∧ Even g
          ∧ (∃ᶠ n in Filter.atTop, gap n = g))
    ∧ ((Finset.image (fun i => 2 * i) (Finset.Icc 1 123)).card = 123)
    ∧ (H1 ≤ (246 : ℕ∞) →
        ∃ g : ℕ, H1 = (g : ℕ∞) ∧ g ∈ Finset.image (fun i => 2 * i) (Finset.Icc 1 123)
          ∧ (∃ᶠ n in Filter.atTop, gap n = g)) := by
  have attained : ∀ (u : ℕ → ℕ) (g : ℕ),
      Filter.liminf (fun n => (u n : ℕ∞)) Filter.atTop = (g : ℕ∞) →
      (∀ᶠ n in Filter.atTop, g ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = g) := by
    intro u g hL
    have hev : ∀ᶠ n in Filter.atTop, g ≤ u n := by
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · exact Filter.Eventually.of_forall (fun n => Nat.zero_le _)
      · have hlt : ((g - 1 : ℕ) : ℕ∞) < Filter.liminf (fun n => (u n : ℕ∞)) Filter.atTop := by
          rw [hL]; exact_mod_cast Nat.sub_lt hg one_pos
        have h2 := Filter.eventually_lt_of_lt_liminf hlt
        filter_upwards [h2] with n hn
        have : (g - 1) < u n := by exact_mod_cast hn
        omega
    refine ⟨hev, ?_⟩
    have hlt2 : Filter.liminf (fun n => (u n : ℕ∞)) Filter.atTop < ((g + 1 : ℕ) : ℕ∞) := by
      rw [hL]; exact_mod_cast Nat.lt_succ_self g
    refine ((Filter.frequently_lt_of_liminf_lt (h := hlt2)).and_eventually hev).mono ?_
    rintro n ⟨h1, h2⟩
    have : u n < g + 1 := by exact_mod_cast h1
    omega
  have hmono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hltn : ∀ n : ℕ, Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    fun n => hmono (Nat.lt_succ_self n)
  have hgap : ∀ n : ℕ, 1 ≤ n → 2 ≤ gap n ∧ Even (gap n) := by
    intro n hn
    have h1 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n := hmono.monotone hn
    rw [Nat.nth_prime_one_eq_three] at h1
    obtain ⟨a, ha⟩ := (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by have := hltn n; omega)
    have h2 := hltn n
    unfold gap
    exact ⟨by omega, ⟨b - a, by omega⟩⟩
  have partB : ∀ g : ℕ, H1 = (g : ℕ∞) →
      2 ≤ g ∧ Even g ∧ (∃ᶠ n in Filter.atTop, gap n = g) := by
    intro g hg
    obtain ⟨-, hfr⟩ := attained gap g hg
    have hone : ∀ᶠ n in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
    obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually hone).exists
    obtain ⟨h2, he⟩ := hgap n hn2
    exact ⟨hn1 ▸ h2, hn1 ▸ he, hfr⟩
  have partC : ∀ B : ℕ, H1 ≤ (B : ℕ∞) →
      ∃ g : ℕ, H1 = (g : ℕ∞) ∧ 2 ≤ g ∧ g ≤ B ∧ Even g
        ∧ (∃ᶠ n in Filter.atTop, gap n = g) := by
    intro B hB
    have hne : H1 ≠ ⊤ := by
      intro h; rw [h] at hB; exact absurd hB (by simp)
    obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hne
    have hg' : H1 = (g : ℕ∞) := hg.symm
    obtain ⟨h2, he, hfr⟩ := partB g hg'
    refine ⟨g, hg', h2, ?_, he, hfr⟩
    rw [hg'] at hB
    exact_mod_cast hB
  have hcard : (Finset.image (fun i => 2 * i) (Finset.Icc 1 123)).card = 123 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
    simp
  refine ⟨attained, partB, partC, hcard, ?_⟩
  intro hB
  obtain ⟨g, hg, h2, hle, ⟨r, hr⟩, hfr⟩ := partC 246 (by exact_mod_cast hB)
  refine ⟨g, hg, ?_, hfr⟩
  rw [Finset.mem_image]
  exact ⟨r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩

end Submissions.TwinPrimesH1Live.LiminfAttained
