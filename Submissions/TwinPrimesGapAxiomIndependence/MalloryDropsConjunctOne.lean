import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Filter.Cofinite

open Filter

namespace Submissions.TwinPrimesGapAxiomIndependence.MalloryDropsConjunctOne


theorem liminf_attained (u : ℕ → ℕ∞) (m : ℕ)
    (h : Filter.liminf u Filter.atTop = (m : ℕ∞)) :
    (∀ᶠ n in Filter.atTop, (m : ℕ∞) ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = (m : ℕ∞)) := by
  have hev : ∀ᶠ n in Filter.atTop, (m : ℕ∞) ≤ u n := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hlt : ((m - 1 : ℕ) : ℕ∞) < Filter.liminf u Filter.atTop := by
        rw [h]; exact_mod_cast Nat.sub_lt hm one_pos
      have hE := Filter.eventually_lt_of_lt_liminf hlt
      filter_upwards [hE] with n hn
      rcases eq_or_ne (u n) ⊤ with h' | h'
      · rw [h']; exact le_top
      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h'
        rw [← hk] at hn ⊢
        have hk' : m - 1 < k := by exact_mod_cast hn
        have hmk : m ≤ k := by omega
        exact_mod_cast hmk
  refine ⟨hev, ?_⟩
  have hfr : ∃ᶠ n in Filter.atTop, u n ≤ (m : ℕ∞) := by
    by_contra hc
    rw [Filter.not_frequently] at hc
    have hev2 : ∀ᶠ n in Filter.atTop, ((m + 1 : ℕ) : ℕ∞) ≤ u n := by
      filter_upwards [hc] with n hn
      have hlt : (m : ℕ∞) < u n := lt_of_not_ge hn
      rcases eq_or_ne (u n) ⊤ with h' | h'
      · rw [h']; exact le_top
      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h'
        rw [← hk] at hlt ⊢
        have hk' : m < k := by exact_mod_cast hlt
        exact_mod_cast hk'
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ Filter.liminf u Filter.atTop := by
      rw [Filter.liminf_eq]; exact le_sSup hev2
    rw [h] at hle
    have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
    omega
  exact (hfr.and_eventually hev).mono (fun n hn => le_antisymm hn.1 hn.2)

/-- A pseudo-enumeration whose gaps are `1, 4, 4, 4, …`. -/
def A (n : ℕ) : ℕ := if n = 0 then 2 else 4 * n - 1

/-- A pseudo-enumeration whose gaps are `1, 2, 2, 2, …`. -/
def B (n : ℕ) : ℕ := if n = 0 then 2 else 2 * n + 1

/-- Everything this problem's graph has proved about the prime gap sequence, as a predicate
on sequences: strictly increasing, starting `2, 3`, every gap from index `1` even and at
least `2`, and a liminf at most the recorded ceiling `246`. -/
def Rec (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ a 0 = 2 ∧ a 1 = 3
  ∧ (∀ n : ℕ, 1 ≤ n → 2 ≤ a (n + 1) - a n ∧ Even (a (n + 1) - a n))
  ∧ Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop ≤ 246

theorem A_gap {n : ℕ} (hn : 1 ≤ n) : A (n + 1) - A n = 4 := by
  unfold A
  rw [if_neg (by omega : ¬ (n + 1 = 0)), if_neg (by omega : ¬ (n = 0))]
  omega

theorem B_gap {n : ℕ} (hn : 1 ≤ n) : B (n + 1) - B n = 2 := by
  unfold B
  rw [if_neg (by omega : ¬ (n + 1 = 0)), if_neg (by omega : ¬ (n = 0))]
  omega

theorem A_mono : StrictMono A := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [A]
  · unfold A
    rw [if_neg (by omega : ¬ (n + 1 = 0)), if_neg (by omega : ¬ (n = 0))]
    omega

theorem B_mono : StrictMono B := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [B]
  · unfold B
    rw [if_neg (by omega : ¬ (n + 1 = 0)), if_neg (by omega : ¬ (n = 0))]
    omega

theorem A_liminf :
    Filter.liminf (fun n => ((A (n + 1) - A n : ℕ) : ℕ∞)) Filter.atTop = 4 := by
  have h : ∀ᶠ n in Filter.atTop, ((A (n + 1) - A n : ℕ) : ℕ∞) = (4 : ℕ∞) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [A_gap hn]; norm_num
  calc Filter.liminf (fun n => ((A (n + 1) - A n : ℕ) : ℕ∞)) Filter.atTop
      = Filter.liminf (fun _ : ℕ => (4 : ℕ∞)) Filter.atTop := Filter.liminf_congr h
    _ = 4 := Filter.liminf_const 4

theorem B_liminf :
    Filter.liminf (fun n => ((B (n + 1) - B n : ℕ) : ℕ∞)) Filter.atTop = 2 := by
  have h : ∀ᶠ n in Filter.atTop, ((B (n + 1) - B n : ℕ) : ℕ∞) = (2 : ℕ∞) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [B_gap hn]; norm_num
  calc Filter.liminf (fun n => ((B (n + 1) - B n : ℕ) : ℕ∞)) Filter.atTop
      = Filter.liminf (fun _ : ℕ => (2 : ℕ∞)) Filter.atTop := Filter.liminf_congr h
    _ = 2 := Filter.liminf_const 2

theorem A_rec : Rec A := by
  refine ⟨A_mono, by norm_num [A], by norm_num [A], fun n hn => ?_, ?_⟩
  · rw [A_gap hn]; exact ⟨by omega, by decide⟩
  · rw [A_liminf]; decide

theorem B_rec : Rec B := by
  refine ⟨B_mono, by norm_num [B], by norm_num [B], fun n hn => ?_, ?_⟩
  · rw [B_gap hn]; exact ⟨by omega, by decide⟩
  · rw [B_liminf]; decide

theorem rec_even (a : ℕ → ℕ) (ha : Rec a) (m : ℕ)
    (hm : Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop = (m : ℕ∞)) :
    2 ≤ m ∧ Even m := by
  have hfr := (liminf_attained (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) m hm).2
  have hfr2 : ∃ᶠ n in Filter.atTop, a (n + 1) - a n = m :=
    hfr.mono (fun n hn => by exact_mod_cast hn)
  obtain ⟨n, hn1, hn2⟩ := Filter.frequently_atTop.mp hfr2 1
  obtain ⟨h2, he⟩ := ha.2.2.2.1 n hn1
  exact ⟨hn2 ▸ h2, hn2 ▸ he⟩

theorem rec_ne_three (a : ℕ → ℕ) (ha : Rec a) :
    Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop ≠ 3 := by
  intro h
  have h3 : Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop = ((3 : ℕ) : ℕ∞) := by
    rw [h]; norm_num
  obtain ⟨_, he⟩ := rec_even a ha 3 h3
  exact absurd he (by decide)

theorem no_entail : ¬ ∀ a : ℕ → ℕ, Rec a → ∃ᶠ n in Filter.atTop, a (n + 1) - a n = 2 := by
  intro hcon
  obtain ⟨n, hn1, hn2⟩ := Filter.frequently_atTop.mp (hcon A A_rec) 1
  rw [A_gap hn1] at hn2
  omega

/-- MUST-FAIL CONTROL.  This is the canonical statement with its FIRST conjunct - the
elimination itself, `¬ ∀ a, Rec a → ∃ᶠ n, a (n+1) - a n = 2` - deleted.  Everything that
remains is true and is proved here, so the module builds and the axiom audit is clean; the
only thing wrong with it is that it is a strictly weaker proposition than the one it is
filed against.  It is expected to red with reason `restatement`.  If it went green, the
anti-restatement bridge would not be discriminating on this statement and the green on
`TwoModels` would mean nothing. -/
theorem proof :
  (Rec A ∧ Filter.liminf (fun n => ((A (n + 1) - A n : ℕ) : ℕ∞)) Filter.atTop = 4
      ∧ ∀ n : ℕ, 1 ≤ n → A (n + 1) - A n ≠ 2)
  ∧ (Rec B ∧ Filter.liminf (fun n => ((B (n + 1) - B n : ℕ) : ℕ∞)) Filter.atTop = 2
      ∧ ∀ n : ℕ, 1 ≤ n → B (n + 1) - B n = 2)
  ∧ (∀ a : ℕ → ℕ, Rec a → ∀ m : ℕ,
      Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop = (m : ℕ∞) →
      2 ≤ m ∧ Even m)
  ∧ (∀ a : ℕ → ℕ, Rec a →
      Filter.liminf (fun n => ((a (n + 1) - a n : ℕ) : ℕ∞)) Filter.atTop ≠ 3) :=
  ⟨⟨A_rec, A_liminf, fun n hn => by rw [A_gap hn]; omega⟩,
   ⟨B_rec, B_liminf, fun n hn => B_gap hn⟩,
   rec_even,
   rec_ne_three⟩

end Submissions.TwinPrimesGapAxiomIndependence.MalloryDropsConjunctOne
