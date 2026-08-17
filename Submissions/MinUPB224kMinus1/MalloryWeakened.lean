import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
DELIBERATELY DEGENERATE. This is the poser's own red smoke test for problem
`MinUPB224kMinus1`.

It has the same outer shape as the canonical statement -- same `∀ k, 2 ≤ k`, same three
existentials over `Fin (4*k+2)`, same nonzero-ness clauses -- but the two clauses that carry
all the mathematics, pairwise orthogonality and unextendibility, have been replaced by `True`.

What is below is a true theorem with a real proof, and it is NOT the theorem that was asked.
The verifier must reject it at the anti-restatement check. If it ever goes green, the problem
does not constrain anything and should not have been posed.
-/

namespace Submissions.MinUPB224kMinus1.MalloryWeakened

theorem proof :
    ∀ k : ℕ, 2 ≤ k →
      ∃ u : Fin (4 * k + 2) → Fin 2 → ℂ,
      ∃ w : Fin (4 * k + 2) → Fin 2 → ℂ,
      ∃ z : Fin (4 * k + 2) → Fin (4 * k - 1) → ℂ,
        (∀ i, u i ≠ 0) ∧
        (∀ i, w i ≠ 0) ∧
        (∀ i, z i ≠ 0) ∧
        (∀ i j : Fin (4 * k + 2), i ≠ j → True) ∧
        (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
          ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
          ∃ _i : Fin (4 * k + 2), True) := by
  intro k hk
  have hd : 0 < 4 * k - 1 := by omega
  refine ⟨fun _ => fun _ => 1, fun _ => fun _ => 1, fun _ => fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  · intro i h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  · intro i h
    have := congrFun h ⟨0, hd⟩
    simp at this
  · intro i j _; trivial
  · intro a _ b _ c _
    exact ⟨⟨0, by omega⟩, trivial⟩

end Submissions.MinUPB224kMinus1.MalloryWeakened
