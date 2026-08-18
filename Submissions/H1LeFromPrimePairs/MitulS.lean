import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

namespace Submissions.H1LeFromPrimePairs.MitulS

noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

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
      unfold gap
      rw [hnthp]
      omega
    exact_mod_cast hgap

theorem proof :
    (∀ d : ℕ,
        (∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ q ≤ p + d ∧ Nat.Prime p ∧ Nat.Prime q) →
        H1 ≤ (d : ℕ∞))
    ∧ (∀ (T : Finset ℕ) (d : ℕ),
        (∀ x ∈ T, x ≤ d) →
        (∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ a ∈ T, ∃ b ∈ T,
            a ≠ b ∧ Nat.Prime (n + a) ∧ Nat.Prime (n + b)) →
        H1 ≤ (d : ℕ∞))
    ∧ ((∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) → H1 ≤ 2) := by
  refine ⟨key, ?_, ?_⟩
  · intro T d hTd hDHL
    refine key d ?_
    intro N
    obtain ⟨n, hNn, a, haT, b, hbT, hab, hpa, hpb⟩ := hDHL N
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact ⟨n + a, n + b, by omega, by omega, by have := hTd b hbT; omega, hpa, hpb⟩
    · exact ⟨n + b, n + a, by omega, by omega, by have := hTd a haT; omega, hpb, hpa⟩
  · intro htwin
    have := key 2 ?_
    · simpa using this
    · intro N
      obtain ⟨p, hNp, hp, hp2⟩ := htwin N
      exact ⟨p, p + 2, hNp, by omega, by omega, hp, hp2⟩

end Submissions.H1LeFromPrimePairs.MitulS
