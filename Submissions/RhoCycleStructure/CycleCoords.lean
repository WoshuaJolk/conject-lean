import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Proof of `Statements.RhoCycleStructure.statement`. Definitions re-declared verbatim. -/

namespace Submissions.RhoCycleStructure.CycleCoords


/-- `ρ`, the step-2 map. Identical to `Statements.TauNormalForm.rho`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

/-- Cycle-coordinates for `ρ`: the relabelling under which `ρ` becomes `+1 mod k`. -/
def phi (k j : ℕ) : ℕ := if j = 1 then 0 else if j % 2 = 0 then j / 2 else (j + k) / 2 - 1

theorem phi_lt (k j : ℕ) (hk : 5 ≤ k) (ho : k % 2 = 1) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    phi k j < k := by
  unfold phi; split_ifs <;> omega

theorem phi_inj (k i j : ℕ) (hk : 5 ≤ k) (ho : k % 2 = 1)
    (a : 1 ≤ i) (b : i ≤ k) (c : 1 ≤ j) (d : j ≤ k) (h : phi k i = phi k j) : i = j := by
  unfold phi at h; split_ifs at h <;> omega

theorem phi_wrap (k j : ℕ) (hk : 5 ≤ k) (ho : k % 2 = 1) (h1 : 1 ≤ j) (h2 : j ≤ k)
    (hw : phi k j + 1 = k) : phi k (rho k j) = 0 := by
  unfold phi rho at *; split_ifs at * <;> omega

theorem phi_step (k j : ℕ) (hk : 5 ≤ k) (ho : k % 2 = 1) (h1 : 1 ≤ j) (h2 : j ≤ k)
    (hs : phi k j + 1 < k) : phi k (rho k j) = phi k j + 1 := by
  unfold phi rho at *; split_ifs at * <;> omega

theorem phi_ends (k : ℕ) (hk : 5 ≤ k) (ho : k % 2 = 1) :
    phi k (k - 1) = (k - 1) / 2 ∧ phi k k = k - 1 ∧ phi k k - phi k (k - 1) = (k - 1) / 2 := by
  unfold phi
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega

theorem proof :
    ∀ k : ℕ, 5 ≤ k → k % 2 = 1 →
      (∀ j : ℕ, 1 ≤ j → j ≤ k → phi k j < k) ∧
      (∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → phi k i = phi k j → i = j) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → phi k j + 1 = k → phi k (rho k j) = 0) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → phi k j + 1 < k → phi k (rho k j) = phi k j + 1) ∧
      (phi k (k - 1) = (k - 1) / 2 ∧ phi k k = k - 1 ∧
        phi k k - phi k (k - 1) = (k - 1) / 2) := by
  intro k hk ho
  exact ⟨fun j a b => phi_lt k j hk ho a b,
         fun i j a b c d h => phi_inj k i j hk ho a b c d h,
         fun j a b h => phi_wrap k j hk ho a b h,
         fun j a b h => phi_step k j hk ho a b h,
         phi_ends k hk ho⟩

end Submissions.RhoCycleStructure.CycleCoords
