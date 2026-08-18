import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Image
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
`DHL[50,2] → H₁ ≤ 246`, unconditionally.

Two independent halves, both discharged here:

* the **tuple**: Engelsma's admissible 50-tuple of diameter 246.  Admissibility is checked
  by the kernel over every modulus `2 ≤ m ≤ 50` via a witness table (no primality decision
  procedure runs in the kernel), and by pigeonhole for `p > 50`.
* the **liminf step**: two primes at distance `≤ d`, at arbitrarily large heights, force a
  *consecutive* prime pair at distance `≤ d` at arbitrarily large index, hence `H₁ ≤ d`.

Controls run before submission, each confirmed to break the build:
perturbing one tuple entry (4 → 1) leaves card / endpoints / bounds intact and fails only
admissibility; weakening "for every N" to a single pair fails; loosening `q ≤ p + d` to
`q ≤ p + d + 1` fails; dropping `Nat.Prime q` fails.
-/

set_option maxRecDepth 8000

namespace Submissions.DHL50ImpliesH1Le246.MitulS

noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- Engelsma's optimal narrow admissible 50-tuple of diameter 246. -/
def L : List ℕ :=
  [0, 4, 6, 16, 30, 34, 36, 46, 48, 58, 60, 64, 70, 78, 84, 88, 90, 94, 100, 106, 108, 114,
   118, 126, 130, 136, 144, 148, 150, 156, 160, 168, 174, 178, 184, 190, 196, 198, 204,
   210, 214, 216, 220, 226, 228, 234, 238, 240, 244, 246]

def tuple : Finset ℕ := L.toFinset

/-- A residue class mod `m` omitted by `L`, for `2 ≤ m ≤ 50`; entries 0,1 are padding. -/
def witTable : List ℕ :=
  [0, 0, 1, 2, 1, 2, 1, 5, 1, 2, 1, 10, 1, 11, 1, 2, 1, 1, 1, 9, 1, 2, 1, 5, 1, 2, 1, 2, 1,
   9, 1, 14, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 1, 18, 1, 5, 1]

def wit (m : ℕ) : ℕ := witTable.getD m 0

theorem card_tuple : tuple.card = 50 := by decide
theorem zero_mem_L : (0 : ℕ) ∈ L := by decide
theorem mem_246_L : (246 : ℕ) ∈ L := by decide
theorem le_246_L : ∀ x ∈ L, x ≤ 246 := by decide

/-- Admissibility below 51, kernel-checked over **all** moduli, prime or not. -/
theorem small : ∀ m < 51, 2 ≤ m → wit m < m ∧ ∀ x ∈ L, x % m ≠ wit m := by decide

theorem admissible : ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ tuple, x % p ≠ r := by
  intro p hp
  by_cases hbig : 50 < p
  · by_contra hcon
    push_neg at hcon
    have hsub : Finset.range p ⊆ tuple.image (fun x => x % p) := by
      intro r hr
      rw [Finset.mem_range] at hr
      obtain ⟨x, hxT, hx⟩ := hcon r hr
      exact Finset.mem_image.mpr ⟨x, hxT, hx⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (tuple.image (fun x => x % p)).card ≤ tuple.card := Finset.card_image_le
    rw [Finset.card_range] at h1
    rw [card_tuple] at h2
    omega
  · push_neg at hbig
    obtain ⟨hlt, hne⟩ := small p (by omega) hp.two_le
    exact ⟨wit p, hlt, fun x hx => hne x (List.mem_toFinset.mp hx)⟩

/-- The liminf step. -/
theorem key (d : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ q ≤ p + d ∧ Nat.Prime p ∧ Nat.Prime q) :
    H1 ≤ (d : ℕ∞) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  refine Filter.liminf_le_of_frequently_le' ?_
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨p, q, hNp, hpq, hqd, hp, hq⟩ := h (Nat.nth Nat.Prime M)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime M) = M :=
      Nat.count_nth_of_infinite hinf M
    have h2 : Nat.count Nat.Prime (Nat.nth Nat.Prime M) ≤ Nat.count Nat.Prime p :=
      Nat.count_monotone Nat.Prime hNp.le
    omega
  · have hnthp : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have e1 : Nat.count Nat.Prime (q + 1) = Nat.count Nat.Prime q + 1 := by
      rw [Nat.count_succ]; simp [hq]
    have e2 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
      rw [Nat.count_succ]; simp [hp]
    have e3 : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q :=
      Nat.count_monotone Nat.Prime (by omega)
    have hnext : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) < q + 1 :=
      Nat.nth_lt_of_lt_count (by omega)
    have hgap : gap (Nat.count Nat.Prime p) ≤ d := by
      unfold gap; rw [hnthp]; omega
    exact_mod_cast hgap

/-- Bounded-diameter version: `DHL`-style pairs inside a tuple of diameter `≤ d` give
`H₁ ≤ d`. -/
theorem fromTuple (T : Finset ℕ) (d : ℕ) (hTd : ∀ x ∈ T, x ≤ d)
    (hDHL : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
        a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)) :
    H1 ≤ (d : ℕ∞) := by
  refine key d ?_
  intro N
  obtain ⟨n, hNn, a, haT, b, hbT, hab, hpa, hpb⟩ := hDHL N
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨n + a, n + b, by omega, by omega, by have := hTd b hbT; omega, hpa, hpb⟩
  · exact ⟨n + b, n + a, by omega, by omega, by have := hTd a haT; omega, hpb, hpa⟩

theorem proof :
    ((∀ T : Finset ℕ, T.card = 50 →
          (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) →
          ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
            a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b))
        → H1 ≤ 246)
    ∧ (∃ T : Finset ℕ,
          T.card = 50 ∧ 0 ∈ T ∧ 246 ∈ T ∧ (∀ x ∈ T, x ≤ 246) ∧
          (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) ∧
          ((∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
              a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)) → H1 ≤ 246)) := by
  have hle : ∀ x ∈ tuple, x ≤ 246 := fun x hx => le_246_L x (List.mem_toFinset.mp hx)
  have hbridge : (∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ tuple, ∃ b ∈ tuple,
      a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)) → H1 ≤ 246 := by
    intro hD
    have := fromTuple tuple 246 hle hD
    simpa using this
  refine ⟨fun hDHL => hbridge (hDHL tuple card_tuple admissible), ?_⟩
  exact ⟨tuple, card_tuple, List.mem_toFinset.mpr zero_mem_L,
    List.mem_toFinset.mpr mem_246_L, hle, admissible, hbridge⟩

end Submissions.DHL50ImpliesH1Le246.MitulS
