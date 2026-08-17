import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.ZMod.Basic

namespace Submissions.PansiotCycleDistanceRigidity.CycleDistance

def c (k : ℕ) : Equiv.Perm (ZMod k) := Equiv.addRight (1 : ZMod k)

abbrev statement : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ m : ZMod k,
    (∃ ψ : Equiv.Perm (ZMod k),
        ψ * c k * ψ⁻¹ = c k ∧ ψ * Equiv.swap 0 m * ψ⁻¹ = Equiv.swap 0 1)
      ↔ (m = 1 ∨ m = -1)

theorem c_apply (k : ℕ) (x : ZMod k) : c k x = x + 1 := rfl

/-- Centraliser of the standard cycle: every commuting permutation is a translation. -/
theorem centraliser {k : ℕ} [NeZero k] (ψ : Equiv.Perm (ZMod k))
    (h : ψ * c k * ψ⁻¹ = c k) : ∀ x, ψ x = ψ 0 + x := by
  have hcomm : ψ * c k = c k * ψ := by
    have := congrArg (· * ψ) h
    simpa [mul_assoc] using this
  have hstep : ∀ x, ψ (x + 1) = ψ x + 1 := by
    intro x
    have := congrArg (fun (f : Equiv.Perm (ZMod k)) => f x) hcomm
    simpa [Equiv.Perm.mul_apply, c_apply] using this
  have hnat : ∀ n : ℕ, ψ ((n : ZMod k)) = ψ 0 + (n : ZMod k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have : ((n + 1 : ℕ) : ZMod k) = (n : ZMod k) + 1 := by push_cast; ring
        rw [this, hstep, ih, add_assoc]
  intro x
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective (n := k) x
  exact hnat n

theorem proof : statement := by
  intro k hk m
  haveI : NeZero k := ⟨by omega⟩
  haveI : Fact (1 < k) := ⟨by omega⟩
  have h10 : (1 : ZMod k) ≠ 0 := one_ne_zero
  constructor
  · rintro ⟨ψ, h1, h2⟩
    have htr := centraliser ψ h1
    have hswap : Equiv.swap (ψ 0) (ψ m) = Equiv.swap 0 1 := by
      rw [Equiv.swap_apply_apply]; exact h2
    rw [htr m] at hswap
    obtain ⟨j, hj0⟩ : ∃ j, ψ 0 = j := ⟨_, rfl⟩
    rw [hj0] at hswap
    by_cases hj : j = 0
    · subst hj
      have h0 := congrArg (fun (f : Equiv.Perm (ZMod k)) => f 0) hswap
      simp only [Equiv.swap_apply_left, zero_add] at h0
      exact Or.inl h0
    · by_cases hjm : j + m = 0
      · rw [hjm] at hswap
        have h0 := congrArg (fun (f : Equiv.Perm (ZMod k)) => f 0) hswap
        simp only [Equiv.swap_apply_right, Equiv.swap_apply_left] at h0
        have hmj : m = -j := eq_neg_of_add_eq_zero_right hjm
        rw [hmj, h0]
        exact Or.inr rfl
      · exfalso
        have h0 := congrArg (fun (f : Equiv.Perm (ZMod k)) => f 0) hswap
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hjm),
          Equiv.swap_apply_left] at h0
        exact h10 h0.symm
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨c k, mul_inv_cancel_right (c k) (c k), ?_⟩
      rw [← Equiv.swap_apply_apply]
      simp [c_apply, Equiv.swap_comm]

end Submissions.PansiotCycleDistanceRigidity.CycleDistance
