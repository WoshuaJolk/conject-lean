import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Route: substitute the three defining equations, then finish by finite case analysis on the
`Fin 10` indices. Nonzero-ness is witnessed coordinatewise: for each row, `Function.ne_iff`
plus the index of an entry that is visibly nonzero, with the entry named in a `show` so that
no simp-normal-form question arises. Orthogonality expands the three inner
products with `Fin.sum_univ_succ` and closes each of the ninety off-diagonal ordered pairs by
`norm_num` together with `Complex.conj_ofNat`, since the conjugate of a numeral is not
reduced by `norm_num` alone; the ten diagonal pairs are discharged from the `i ≠ j` hypothesis.

`maxHeartbeats` is raised because all hundred index pairs are elaborated inside a single
declaration and the default budget is per-declaration, not per-goal.

Recorded for the next contributor: an earlier draft of this proof drove the orthogonality
goals with bare `simp [Fin.sum_univ_succ]`, and on this Mathlib revision that crashes the
elaborator outright (`PANIC at Lean.Expr.appArg!: application expected`) under a narrow
import set, while succeeding under a full `import Mathlib`. Routing the same goals through
`norm_num` with the conjugation lemmas named explicitly avoids the bad simp procedure
entirely and, incidentally, cuts elaboration from about 300 seconds to about 40.

No `decide`, no `native_decide`, no numerics -- every entry is an integer literal in `ℂ`,
so `star` is inert and the result holds over `ℝ` and `ℂ` alike.
-/

namespace Submissions.UPBWitness227Orthogonal.IntegerWitness

set_option maxHeartbeats 2000000 in
theorem proof :
  ∀ u : Fin 10 → Fin 2 → ℂ, ∀ w : Fin 10 → Fin 2 → ℂ, ∀ z : Fin 10 → Fin 7 → ℂ,
    u = ![![1, 0],
     ![1, 0],
     ![0, 1],
     ![0, 1],
     ![1, 1],
     ![1, 1],
     ![1, (-1)],
     ![1, (-1)],
     ![1, 2],
     ![2, (-1)]] →
    w = ![![1, 1],
     ![1, 3],
     ![1, 4],
     ![1, 5],
     ![1, 2],
     ![(-4), 1],
     ![(-3), 1],
     ![(-5), 1],
     ![(-1), 1],
     ![(-2), 1]] →
    z = ![![0, 0, (-6), (-5), 1, 1, 0],
     ![1, 0, 0, 0, 0, 0, 0],
     ![5, (-4), (-2), 0, 0, 0, 0],
     ![0, (-3), 6, 1, 1, 0, 0],
     ![0, 0, 0, (-1), 1, (-6), 1],
     ![0, 2, 2, (-3), (-3), 0, 0],
     ![2, 2, 1, (-1), 1, 0, 0],
     ![0, 1, (-2), 3, 3, 0, 0],
     ![0, 0, 0, 0, 0, (-1), (-6)],
     ![0, 0, 0, 0, 0, 0, 1]] →
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) := by
  intro u w z hu hw hz
  subst hu; subst hw; subst hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (2 : ℂ) ≠ 0; norm_num⟩
  · intro i
    fin_cases i
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (-4 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (-3 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (-5 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (-1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (-2 : ℂ) ≠ 0; norm_num⟩
  · intro i
    fin_cases i
    · rw [Function.ne_iff]; exact ⟨2, by show (-6 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (5 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show (-3 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨3, by show (-1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show (2 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show (2 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show (1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨5, by show (-1 : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨6, by show (1 : ℂ) ≠ 0; norm_num⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | norm_num [Fin.sum_univ_succ, Complex.conj_ofNat, Complex.conj_natCast]

end Submissions.UPBWitness227Orthogonal.IntegerWitness
