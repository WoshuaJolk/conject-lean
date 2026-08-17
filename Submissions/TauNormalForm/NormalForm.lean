import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Proof of `Statements.TauNormalForm.statement`. Definitions re-declared verbatim; a
submission may not import `Statements.*`, and the anti-restatement bridge checks them for
definitional equality against the canonical file. -/

namespace Submissions.TauNormalForm.NormalForm


/-- `σ(m)` on the letter `j`: fixes `1,…,m-1`, shifts `m ≤ j ≤ k-1` up by one, sends `k ↦ m`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `ρ`, the step-2 map: `1 ↦ 2`, `j ↦ j+2` for `2 ≤ j ≤ k-2`, `k-1 ↦ 3`, `k ↦ 1`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

/-- The transposition `(k-1, k)`, i.e. `τ(1)⁻¹τ(2)`. -/
def swapLast (k j : ℕ) : ℕ := if j = k - 1 then k else if j = k then k - 1 else j

/-- The transposition `(1, k)`, i.e. `σ(1)⁻¹σ(2)`. -/
def swapEnds (k j : ℕ) : ℕ := if j = 1 then k else if j = k then 1 else j

theorem sig_range (k m j : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    1 ≤ sig k m j ∧ sig k m j ≤ k := by
  unfold sig; split_ifs <;> omega

theorem sig_inj (k m i j : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) (hi : 1 ≤ i) (hik : i ≤ k)
    (hj : 1 ≤ j) (hjk : j ≤ k) (h : sig k m i = sig k m j) : i = j := by
  unfold sig at h; split_ifs at h <;> omega

theorem tau_one (k j : ℕ) (hk : 4 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    sig k 3 (sig k 1 j) = rho k j := by
  unfold sig rho; split_ifs <;> omega

theorem tau_two (k j : ℕ) (hk : 4 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    sig k 1 (sig k 2 j) = rho k (swapLast k j) := by
  unfold sig rho swapLast; split_ifs <;> omega

theorem pansiot_pair (k j : ℕ) (hk : 4 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    sig k 2 j = sig k 1 (swapEnds k j) := by
  unfold sig swapEnds; split_ifs <;> omega

theorem proof :
    ∀ k : ℕ, 4 ≤ k →
      (∀ m j : ℕ, 1 ≤ m → m ≤ k → 1 ≤ j → j ≤ k → 1 ≤ sig k m j ∧ sig k m j ≤ k) ∧
      (∀ m i j : ℕ, 1 ≤ m → m ≤ k → 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
          sig k m i = sig k m j → i = j) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 3 (sig k 1 j) = rho k j) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 1 (sig k 2 j) = rho k (swapLast k j)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 2 j = sig k 1 (swapEnds k j)) := by
  intro k hk
  exact ⟨fun m j a b c d => sig_range k m j a b c d,
         fun m i j a b c d e f g => sig_inj k m i j a b c d e f g,
         fun j a b => tau_one k j hk a b,
         fun j a b => tau_two k j hk a b,
         fun j a b => pansiot_pair k j hk a b⟩

end Submissions.TauNormalForm.NormalForm
