import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

set_option maxRecDepth 100000

namespace Submissions.TwinPrimesH1ENat.Bridge

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁` as an element of `ℕ∞`, so that the `sSup` inside `liminf` is the honest supremum. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The gap sequence starts `1, 2, 2, 4`; `H₁ ≥ 2` unconditionally; `H₁ = 2` is equivalent to
the twin prime conjecture; and the `ℕ` liminf convention is junk where the `ℕ∞` one is not.

The two directions of the equivalence are the only real content.  `H₁ = 2 → twin primes`:
were there no twin pair beyond `N`, then for every index `b` with `Nat.nth Nat.Prime b > N`
the gap at `b` could not be `2`, hence is `≥ 3` since it is `≥ 2` already; that puts `3` in
the set the `sSup` is taken over and gives `3 ≤ H₁`.  `twin primes → H₁ = 2`: for a twin
pair `(p, p + 2)` with `p > 2`, `p + 1` is even and exceeds `2`, so it is composite and
`p, p + 2` are consecutive primes; `Nat.count`/`Nat.nth` turn that into
`gap (Nat.count Nat.Prime p) = 2`, and `Nat.nth_lt_nth` pushes the index past any bound, so
gaps equal to `2` occur frequently and no `a` with `a ≤ gap n` eventually can exceed `2`. -/
theorem proof :
  (gap 0 = 1 ∧ gap 1 = 2 ∧ gap 2 = 2 ∧ gap 3 = 4)
  ∧ 2 ≤ H1
  ∧ (H1 = 2 ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
  ∧ (Filter.liminf (fun n : ℕ => n) Filter.atTop = 0
      ∧ Filter.liminf (fun n : ℕ => (n : ℕ∞)) Filter.atTop = ⊤) := by
  have hmono : StrictMono (Nat.nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hlt : ∀ n : ℕ, Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    fun n => hmono (Nat.lt_succ_self n)
  have hgap2 : ∀ n : ℕ, 1 ≤ n → 2 ≤ gap n := by
    intro n hn
    have h1 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n := hmono.monotone hn
    rw [Nat.nth_prime_one_eq_three] at h1
    obtain ⟨a, ha⟩ := (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
    obtain ⟨b, hb⟩ := (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by
      have := hlt n; omega)
    have h2 := hlt n
    unfold gap
    omega
  have hodd : ∀ p : ℕ, Nat.Prime p → 2 < p → ¬ Nat.Prime (p + 1) := by
    intro p hp hp2 h1
    have h : Even (p + 1) := (hp.odd_of_ne_two (by omega)).add_one
    have := (Nat.Prime.even_iff h1).mp h
    omega
  have hH1ge : 2 ≤ H1 := by
    unfold H1
    rw [Filter.liminf_eq]
    refine le_sSup ?_
    refine Filter.eventually_atTop.mpr ⟨1, fun b hb => ?_⟩
    exact_mod_cast hgap2 b hb
  refine ⟨⟨by simp [gap], by simp [gap], by simp [gap], by simp [gap]⟩, hH1ge, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `H₁ = 2` forces twin primes beyond every bound
    intro hH1 N
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ n in Filter.atTop, (3 : ℕ∞) ≤ (gap n : ℕ∞) := by
      refine Filter.eventually_atTop.mpr ⟨N + 1, fun b hb => ?_⟩
      have hb1 : 1 ≤ b := by omega
      have h2 := hgap2 b hb1
      have hbig : N < Nat.nth Nat.Prime b := by
        have := Nat.add_two_le_nth_prime b; omega
      have h3 : 3 ≤ gap b := by
        rcases Nat.lt_or_ge (gap b) 3 with h | h
        · exfalso
          have hg : gap b = 2 := by omega
          have hstep : Nat.nth Nat.Prime (b + 1) = Nat.nth Nat.Prime b + 2 := by
            have := hlt b
            unfold gap at hg
            omega
          have hno := hcon (Nat.nth Nat.Prime b) hbig (Nat.prime_nth_prime b)
          rw [← hstep] at hno
          exact hno (Nat.prime_nth_prime (b + 1))
        · exact h
      exact_mod_cast h3
    have h3 : (3 : ℕ∞) ≤ H1 := by
      unfold H1; rw [Filter.liminf_eq]; exact le_sSup hev
    rw [hH1] at h3
    exact absurd h3 (by decide)
  · -- twin primes beyond every bound force `H₁ = 2`
    intro tpc
    refine le_antisymm ?_ hH1ge
    have hfr : ∃ᶠ n in Filter.atTop, gap n = 2 := by
      refine Filter.frequently_atTop.mpr ?_
      intro M
      obtain ⟨p, hpN, hp, hp2⟩ := tpc (Nat.nth Nat.Prime M)
      have hM2 : 2 ≤ Nat.nth Nat.Prime M := by
        have := Nat.add_two_le_nth_prime M; omega
      have hpgt : 2 < p := by omega
      have hnp1 : ¬ Nat.Prime (p + 1) := hodd p hp hpgt
      have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
      have hc1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
        rw [Nat.count_succ]; simp [hp]
      have hc2 : Nat.count Nat.Prime (p + 2) = Nat.count Nat.Prime p + 1 := by
        have hpp : p + 2 = (p + 1) + 1 := rfl
        rw [hpp, Nat.count_succ, hc1]; simp [hnp1]
      have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = p + 2 := by
        rw [← hc2]; exact Nat.nth_count hp2
      refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
      · have hlt' : Nat.nth Nat.Prime M < Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
          rw [h1]; exact hpN
        exact le_of_lt ((Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hlt')
      · unfold gap
        rw [h1, h2]
        omega
    unfold H1
    rw [Filter.liminf_eq]
    refine sSup_le ?_
    intro a ha
    obtain ⟨n, hn1, hn2⟩ := (ha.and_frequently hfr).exists
    rw [hn2] at hn1
    simpa using hn1
  · -- the `ℕ` convention: an unbounded sequence gets liminf `0`
    rw [Filter.liminf_eq]
    have hset : {a : ℕ | ∀ᶠ n in Filter.atTop, a ≤ n} = Set.univ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Filter.eventually_atTop]
      exact ⟨a, fun b hb => hb⟩
    rw [hset]
    exact Set.Infinite.Nat.sSup_eq_zero Set.infinite_univ
  · -- the `ℕ∞` convention: the same sequence gets liminf `⊤`
    rw [Filter.liminf_eq]
    refine ENat.eq_top_iff_forall_ge.mpr ?_
    intro m
    refine le_sSup ?_
    exact Filter.eventually_atTop.mpr ⟨m, fun b hb => by exact_mod_cast hb⟩

end Submissions.TwinPrimesH1ENat.Bridge
