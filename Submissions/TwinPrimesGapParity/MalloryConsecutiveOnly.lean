import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.TwinPrimesGapParity.MalloryConsecutiveOnly

/-- DELIBERATELY WEAKENED must-fail control.  The pair form only — no indexed form, no
sharpness data, no index-0 exception — and with the *consecutiveness* hypothesis
`∀ r, Nat.Prime r → r ≤ p ∨ q ≤ r` bolted on.  That hypothesis is never used: the parity
argument needs only that both primes exceed `2`.  So this is a true, kernel-checked theorem
that reads almost exactly like the canonical statement and is strictly weaker than it.  It
is filed as a control precisely because "gap between *consecutive* primes" is the phrasing a
reader reaches for first, and the anti-restatement check has to reject it. -/
theorem proof :
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → p < q →
    (∀ r : ℕ, Nat.Prime r → r ≤ p ∨ q ≤ r) →
    2 ≤ q - p ∧ Even (q - p) := by
  intro p q hp hq hp2 hpq _
  obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨b, hb⟩ := hq.odd_of_ne_two (by omega)
  subst ha
  subst hb
  refine ⟨by omega, ?_⟩
  have h : 2 * b + 1 - (2 * a + 1) = 2 * (b - a) := by omega
  rw [h]
  exact even_two_mul _

end Submissions.TwinPrimesGapParity.MalloryConsecutiveOnly
