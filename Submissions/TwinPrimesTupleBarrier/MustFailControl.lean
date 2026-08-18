import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
A DELIBERATE MUST-FAIL CONTROL, submitted with `expect: "red"` and
`expect_reason: "restatement"`.

It drops both the congruence conclusion `p ≡ a [MOD q]` and the compositeness conclusion
`∀ h ∈ H, ¬ Nat.Prime (p + h)` from the canonical statement, keeping only "there are
arbitrarily large primes" — Euclid's theorem, which is in Mathlib and is very much easier
than the theorem this label stands for.

It is submitted to answer the question "could the anti-restatement check have failed?" for
the five proof artifacts filed on this problem by the same run.  If this artifact settles
GREEN, the verifier's definitional-equality bridge is not doing its job and every green on
this problem should be re-examined.  It is expected to settle RED with reason
`restatement`.
-/

namespace Submissions.TwinPrimesTupleBarrier.MustFailControl

/-- Euclid's theorem, dressed in the canonical statement's binders but with the real
conclusions removed. -/
theorem proof :
    ∀ (H : Finset ℕ) (q a N : ℕ), 0 < q → Nat.Coprime a q → (∀ h ∈ H, 0 < h) →
      ∃ p : ℕ, N < p ∧ Nat.Prime p := by
  intro H q a N _ _ _
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p, by omega, hp2⟩

end Submissions.TwinPrimesTupleBarrier.MustFailControl
