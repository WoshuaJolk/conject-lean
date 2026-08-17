import Mathlib

/-!
A DELIBERATE degenerate artifact, submitted by the poser of this problem as a smoke test.

This is the first entry of the degenerate-artifact catalogue: a vacuous hypothesis. It is a
true theorem, it has a real one-line proof, it is sorry-free, it uses no forbidden syntax and
it passes the axiom audit -- and it is NOT the theorem that was asked, because the hypothesis
`0 = 1` never fires. Only the anti-restatement check catches it.

It MUST go red. A verifier that grades this green does not constrain anything.
-/

namespace Submissions.KWiseOddtownConj1.MalloryVacuous

open Finset

def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

theorem proof :
    ∀ k t : ℕ, 2 ≤ t → t ≤ k → k + 2 < 2 * t →
      ∃ C : ℕ, ∀ (n m : ℕ) (A : Fin k → Fin m → Finset (Fin n)),
        (0 = 1) → OVHyp k t m n A → m ^ (k / 2) ≤ C * n := by
  intro k t _ _ _
  exact ⟨0, fun _ _ _ h _ => absurd h (by norm_num)⟩

end Submissions.KWiseOddtownConj1.MalloryVacuous
