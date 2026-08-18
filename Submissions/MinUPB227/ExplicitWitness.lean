import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# f_m(2,2,7) ≤ 10, in the kernel

An explicit unextendible product basis of ten states in `C² ⊗ C² ⊗ C^7`. The states are the
integer-entry witness recorded in `jig.so/reports/41`; their pairwise orthogonality is already
machine-checked as `UPBWitness227Orthogonal`, and what is new here is **unextendibility**.

## How unextendibility is proved without a `3^10` search

Suppose some nonzero `|a⟩ ⊗ |b⟩ ⊗ |c⟩` is orthogonal to all ten states, so for every `i`
`⟨uᵢ|a⟩⟨wᵢ|b⟩⟨zᵢ|c⟩ = 0`.

* A nonzero `a ∈ C²` annihilates exactly those `uᵢ` lying on one line. The ten `uᵢ` fall into
  six parallel classes, pairwise independent, so `a` kills **one class or none**: seven cases.
* Likewise the ten `wᵢ` are pairwise independent directions, so `b` kills **one state or
  none**: eleven cases.
* That leaves `7 × 11 = 77` branches. In each, at most three of the ten indices are killed, so
  at least seven survive with `⟨uᵢ|a⟩ ≠ 0` and `⟨wᵢ|b⟩ ≠ 0`, forcing `⟨zᵢ|c⟩ = 0` for those
  seven.
* For each branch a fixed set `T` of seven surviving indices is chosen whose `zᵢ` are linearly
  independent, and the **inverse of that 7×7 matrix is supplied as explicit rational
  coefficients**. Seven `linear_combination` calls then give `c₀ = ⋯ = c₆ = 0`, contradicting
  `c ≠ 0`.

So the kernel never searches: it checks 39 explicit matrix inverses and some ring identities.
The 77 branches, the choice of `T` in each, and every inverse were computed in exact rational
arithmetic and emitted mechanically; the generator is `k2/gen.py` in the run that produced this.

`maxHeartbeats` is raised because the whole argument lives in one declaration.
No `decide`, no `native_decide`, no `sorry`, no numerics — every constant is an integer or
rational literal in `ℂ`.
-/

namespace Submissions.MinUPB227.ExplicitWitness

/-- If a product of three complex numbers vanishes and the first two do not, the third does. -/
theorem killz {x y z : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (h : x * y * z = 0) : z = 0 := by
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd h1 (mul_ne_zero hx hy)
  · exact h1

/-- Two independent linear forms vanishing on `(x, y)` force `x = y = 0`. This is what makes
"a nonzero `a` kills at most one parallel class" work. -/
theorem pair2 {x y p q r s : ℂ} (hd : p * s - q * r ≠ 0)
    (h1 : p * x + q * y = 0) (h2 : r * x + s * y = 0) : x = 0 ∧ y = 0 := by
  constructor
  · have h : (p * s - q * r) * x = 0 := by linear_combination s * h1 - q * h2
    exact (mul_eq_zero.1 h).resolve_left hd
  · have h : (p * s - q * r) * y = 0 := by linear_combination p * h2 - r * h1
    exact (mul_eq_zero.1 h).resolve_left hd

/-- Spanning certificate for the index set [0, 1, 2, 3, 4, 5, 6]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span0 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (50 / 47 : ℂ) * e1 + (-10 / 47 : ℂ) * e2 + (-3 / 47 : ℂ) * e3 + (-1 / 47 : ℂ) * e5, by linear_combination (35 / 94 : ℂ) * e1 + (-7 / 94 : ℂ) * e2 + (6 / 47 : ℂ) * e3 + (2 / 47 : ℂ) * e5, by linear_combination (513 / 188 : ℂ) * e1 + (-65 / 188 : ℂ) * e2 + (1 / 47 : ℂ) * e3 + (-15 / 94 : ℂ) * e5 + (-1 / 2 : ℂ) * e6, by linear_combination (-333 / 188 : ℂ) * e1 + (29 / 188 : ℂ) * e2 + (1 / 47 : ℂ) * e3 + (-15 / 94 : ℂ) * e5 + (1 / 2 : ℂ) * e6, by linear_combination ((1) : ℂ) * e0 + (1659 / 94 : ℂ) * e1 + (-219 / 94 : ℂ) * e2 + (40 / 47 : ℂ) * e3 + (-18 / 47 : ℂ) * e5 + ((-3) : ℂ) * e6, by linear_combination ((6) : ℂ) * e0 + (10377 / 94 : ℂ) * e1 + (-1361 / 94 : ℂ) * e2 + (240 / 47 : ℂ) * e3 + ((1) : ℂ) * e4 + (-108 / 47 : ℂ) * e5 + ((-19) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 4, 5, 8]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span1 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (50 / 47 : ℂ) * e1 + (-10 / 47 : ℂ) * e2 + (-3 / 47 : ℂ) * e3 + (-1 / 47 : ℂ) * e5, by linear_combination (35 / 94 : ℂ) * e1 + (-7 / 94 : ℂ) * e2 + (6 / 47 : ℂ) * e3 + (2 / 47 : ℂ) * e5, by linear_combination (-37 / 234 : ℂ) * e0 + (-25 / 141 : ℂ) * e1 + (5 / 141 : ℂ) * e2 + (-623 / 5499 : ℂ) * e3 + (-1 / 39 : ℂ) * e4 + (-121 / 1222 : ℂ) * e5 + (-1 / 234 : ℂ) * e6, by linear_combination (37 / 234 : ℂ) * e0 + (160 / 141 : ℂ) * e1 + (-32 / 141 : ℂ) * e2 + (857 / 5499 : ℂ) * e3 + (1 / 39 : ℂ) * e4 + (-269 / 1222 : ℂ) * e5 + (1 / 234 : ℂ) * e6, by linear_combination (2 / 39 : ℂ) * e0 + (10 / 47 : ℂ) * e1 + (-2 / 47 : ℂ) * e2 + (80 / 1833 : ℂ) * e3 + (-2 / 13 : ℂ) * e4 + (-12 / 611 : ℂ) * e5 + (-1 / 39 : ℂ) * e6, by linear_combination (-1 / 117 : ℂ) * e0 + (-5 / 141 : ℂ) * e1 + (1 / 141 : ℂ) * e2 + (-40 / 5499 : ℂ) * e3 + (1 / 39 : ℂ) * e4 + (2 / 611 : ℂ) * e5 + (-19 / 117 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 4, 5, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span2 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (50 / 47 : ℂ) * e1 + (-10 / 47 : ℂ) * e2 + (-3 / 47 : ℂ) * e3 + (-1 / 47 : ℂ) * e5, by linear_combination (35 / 94 : ℂ) * e1 + (-7 / 94 : ℂ) * e2 + (6 / 47 : ℂ) * e3 + (2 / 47 : ℂ) * e5, by linear_combination (-3 / 19 : ℂ) * e0 + (-315 / 1786 : ℂ) * e1 + (63 / 1786 : ℂ) * e2 + (-101 / 893 : ℂ) * e3 + (-1 / 38 : ℂ) * e4 + (-177 / 1786 : ℂ) * e5 + (1 / 38 : ℂ) * e6, by linear_combination (3 / 19 : ℂ) * e0 + (2025 / 1786 : ℂ) * e1 + (-405 / 1786 : ℂ) * e2 + (139 / 893 : ℂ) * e3 + (1 / 38 : ℂ) * e4 + (-393 / 1786 : ℂ) * e5 + (-1 / 38 : ℂ) * e6, by linear_combination (1 / 19 : ℂ) * e0 + (195 / 893 : ℂ) * e1 + (-39 / 893 : ℂ) * e2 + (40 / 893 : ℂ) * e3 + (-3 / 19 : ℂ) * e4 + (-18 / 893 : ℂ) * e5 + (3 / 19 : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 4, 6, 7]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span3 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e5 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination ((1) : ℂ) * e1 + (-1 / 5 : ℂ) * e2 + (-3 / 50 : ℂ) * e3 + (1 / 50 : ℂ) * e6, by linear_combination (1 / 2 : ℂ) * e1 + (-1 / 10 : ℂ) * e2 + (3 / 25 : ℂ) * e3 + (-1 / 25 : ℂ) * e6, by linear_combination (9 / 4 : ℂ) * e1 + (-1 / 4 : ℂ) * e2 + (1 / 20 : ℂ) * e3 + (-1 / 2 : ℂ) * e5 + (3 / 20 : ℂ) * e6, by linear_combination (-9 / 4 : ℂ) * e1 + (1 / 4 : ℂ) * e2 + (1 / 20 : ℂ) * e3 + (1 / 2 : ℂ) * e5 + (3 / 20 : ℂ) * e6, by linear_combination ((1) : ℂ) * e0 + (33 / 2 : ℂ) * e1 + (-21 / 10 : ℂ) * e2 + (23 / 25 : ℂ) * e3 + ((-3) : ℂ) * e5 + (9 / 25 : ℂ) * e6, by linear_combination ((6) : ℂ) * e0 + (207 / 2 : ℂ) * e1 + (-131 / 10 : ℂ) * e2 + (138 / 25 : ℂ) * e3 + ((1) : ℂ) * e4 + ((-19) : ℂ) * e5 + (54 / 25 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 4, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span4 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (-1 / 18 : ℂ) * e0 + (5 / 6 : ℂ) * e1 + (-1 / 6 : ℂ) * e2 + (-1 / 9 : ℂ) * e3 + (1 / 6 : ℂ) * e4 + (-19 / 18 : ℂ) * e5 + (-13 / 2 : ℂ) * e6, by linear_combination (1 / 9 : ℂ) * e0 + (5 / 6 : ℂ) * e1 + (-1 / 6 : ℂ) * e2 + (2 / 9 : ℂ) * e3 + (-1 / 3 : ℂ) * e4 + (19 / 9 : ℂ) * e5 + ((13) : ℂ) * e6, by linear_combination (-5 / 12 : ℂ) * e0 + (-5 / 4 : ℂ) * e1 + (1 / 4 : ℂ) * e2 + (-1 / 3 : ℂ) * e3 + (3 / 4 : ℂ) * e4 + (-59 / 12 : ℂ) * e5 + (-121 / 4 : ℂ) * e6, by linear_combination (-5 / 12 : ℂ) * e0 + (-5 / 4 : ℂ) * e1 + (1 / 4 : ℂ) * e2 + (-1 / 3 : ℂ) * e3 + (7 / 4 : ℂ) * e4 + (-131 / 12 : ℂ) * e5 + (-269 / 4 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 5, 6, 8]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span5 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (50 / 47 : ℂ) * e1 + (-10 / 47 : ℂ) * e2 + (-3 / 47 : ℂ) * e3 + (-1 / 47 : ℂ) * e4, by linear_combination (35 / 94 : ℂ) * e1 + (-7 / 94 : ℂ) * e2 + (6 / 47 : ℂ) * e3 + (2 / 47 : ℂ) * e4, by linear_combination (513 / 188 : ℂ) * e1 + (-65 / 188 : ℂ) * e2 + (1 / 47 : ℂ) * e3 + (-15 / 94 : ℂ) * e4 + (-1 / 2 : ℂ) * e5, by linear_combination (-333 / 188 : ℂ) * e1 + (29 / 188 : ℂ) * e2 + (1 / 47 : ℂ) * e3 + (-15 / 94 : ℂ) * e4 + (1 / 2 : ℂ) * e5, by linear_combination ((1) : ℂ) * e0 + (1659 / 94 : ℂ) * e1 + (-219 / 94 : ℂ) * e2 + (40 / 47 : ℂ) * e3 + (-18 / 47 : ℂ) * e4 + ((-3) : ℂ) * e5, by linear_combination (-1 / 6 : ℂ) * e0 + (-553 / 188 : ℂ) * e1 + (73 / 188 : ℂ) * e2 + (-20 / 141 : ℂ) * e3 + (3 / 47 : ℂ) * e4 + (1 / 2 : ℂ) * e5 + (-1 / 6 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 5, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span6 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (50 / 47 : ℂ) * e1 + (-10 / 47 : ℂ) * e2 + (-3 / 47 : ℂ) * e3 + (-1 / 47 : ℂ) * e4, by linear_combination (35 / 94 : ℂ) * e1 + (-7 / 94 : ℂ) * e2 + (6 / 47 : ℂ) * e3 + (2 / 47 : ℂ) * e4, by linear_combination (-1 / 6 : ℂ) * e0 + (-10 / 47 : ℂ) * e1 + (2 / 47 : ℂ) * e2 + (-17 / 141 : ℂ) * e3 + (-9 / 94 : ℂ) * e4 + (-1 / 6 : ℂ) * e5 + ((-1) : ℂ) * e6, by linear_combination (1 / 6 : ℂ) * e0 + (55 / 47 : ℂ) * e1 + (-11 / 47 : ℂ) * e2 + (23 / 141 : ℂ) * e3 + (-21 / 94 : ℂ) * e4 + (1 / 6 : ℂ) * e5 + ((1) : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 6, 7, 8]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span7 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination ((1) : ℂ) * e1 + (-1 / 5 : ℂ) * e2 + (-3 / 50 : ℂ) * e3 + (1 / 50 : ℂ) * e5, by linear_combination (1 / 2 : ℂ) * e1 + (-1 / 10 : ℂ) * e2 + (3 / 25 : ℂ) * e3 + (-1 / 25 : ℂ) * e5, by linear_combination (9 / 4 : ℂ) * e1 + (-1 / 4 : ℂ) * e2 + (1 / 20 : ℂ) * e3 + (-1 / 2 : ℂ) * e4 + (3 / 20 : ℂ) * e5, by linear_combination (-9 / 4 : ℂ) * e1 + (1 / 4 : ℂ) * e2 + (1 / 20 : ℂ) * e3 + (1 / 2 : ℂ) * e4 + (3 / 20 : ℂ) * e5, by linear_combination ((1) : ℂ) * e0 + (33 / 2 : ℂ) * e1 + (-21 / 10 : ℂ) * e2 + (23 / 25 : ℂ) * e3 + ((-3) : ℂ) * e4 + (9 / 25 : ℂ) * e5, by linear_combination (-1 / 6 : ℂ) * e0 + (-11 / 4 : ℂ) * e1 + (7 / 20 : ℂ) * e2 + (-23 / 150 : ℂ) * e3 + (1 / 2 : ℂ) * e4 + (-3 / 50 : ℂ) * e5 + (-1 / 6 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 6, 7, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span8 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination ((1) : ℂ) * e1 + (-1 / 5 : ℂ) * e2 + (-3 / 50 : ℂ) * e3 + (1 / 50 : ℂ) * e5, by linear_combination (1 / 2 : ℂ) * e1 + (-1 / 10 : ℂ) * e2 + (3 / 25 : ℂ) * e3 + (-1 / 25 : ℂ) * e5, by linear_combination (9 / 4 : ℂ) * e1 + (-1 / 4 : ℂ) * e2 + (1 / 20 : ℂ) * e3 + (-1 / 2 : ℂ) * e4 + (3 / 20 : ℂ) * e5, by linear_combination (-9 / 4 : ℂ) * e1 + (1 / 4 : ℂ) * e2 + (1 / 20 : ℂ) * e3 + (1 / 2 : ℂ) * e4 + (3 / 20 : ℂ) * e5, by linear_combination ((1) : ℂ) * e0 + (33 / 2 : ℂ) * e1 + (-21 / 10 : ℂ) * e2 + (23 / 25 : ℂ) * e3 + ((-3) : ℂ) * e4 + (9 / 25 : ℂ) * e5, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 6, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span9 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (-1 / 18 : ℂ) * e0 + (1 / 12 : ℂ) * e1 + (-1 / 12 : ℂ) * e2 + (-1 / 9 : ℂ) * e3 + (1 / 6 : ℂ) * e4 + (-1 / 18 : ℂ) * e5 + (-1 / 3 : ℂ) * e6, by linear_combination (1 / 9 : ℂ) * e0 + (7 / 3 : ℂ) * e1 + (-1 / 3 : ℂ) * e2 + (2 / 9 : ℂ) * e3 + (-1 / 3 : ℂ) * e4 + (1 / 9 : ℂ) * e5 + (2 / 3 : ℂ) * e6, by linear_combination (-5 / 12 : ℂ) * e0 + (-37 / 8 : ℂ) * e1 + (5 / 8 : ℂ) * e2 + (-1 / 3 : ℂ) * e3 + (3 / 4 : ℂ) * e4 + (-5 / 12 : ℂ) * e5 + (-5 / 2 : ℂ) * e6, by linear_combination (-5 / 12 : ℂ) * e0 + (-73 / 8 : ℂ) * e1 + (9 / 8 : ℂ) * e2 + (-1 / 3 : ℂ) * e3 + (7 / 4 : ℂ) * e4 + (-5 / 12 : ℂ) * e5 + (-5 / 2 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 3, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span10 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination ((1) : ℂ) * e1 + (-1 / 5 : ℂ) * e2 + (-3 / 50 : ℂ) * e3 + (1 / 50 : ℂ) * e4, by linear_combination (1 / 2 : ℂ) * e1 + (-1 / 10 : ℂ) * e2 + (3 / 25 : ℂ) * e3 + (-1 / 25 : ℂ) * e4, by linear_combination (-1 / 6 : ℂ) * e0 + (-1 / 2 : ℂ) * e1 + (1 / 10 : ℂ) * e2 + (-31 / 300 : ℂ) * e3 + (9 / 100 : ℂ) * e4 + (-1 / 6 : ℂ) * e5 + ((-1) : ℂ) * e6, by linear_combination (1 / 6 : ℂ) * e0 + (1 / 2 : ℂ) * e1 + (-1 / 10 : ℂ) * e2 + (61 / 300 : ℂ) * e3 + (21 / 100 : ℂ) * e4 + (1 / 6 : ℂ) * e5 + ((1) : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 4, 5, 6, 7]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span11 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (1 / 3 : ℂ) * e4 + (1 / 3 : ℂ) * e6, by linear_combination (5 / 2 : ℂ) * e1 + (-1 / 2 : ℂ) * e2 + (-2 / 3 : ℂ) * e4 + (-2 / 3 : ℂ) * e6, by linear_combination (37 / 12 : ℂ) * e1 + (-5 / 12 : ℂ) * e2 + (-5 / 18 : ℂ) * e4 + (-1 / 2 : ℂ) * e5 + (-1 / 9 : ℂ) * e6, by linear_combination (-17 / 12 : ℂ) * e1 + (1 / 12 : ℂ) * e2 + (-5 / 18 : ℂ) * e4 + (1 / 2 : ℂ) * e5 + (-1 / 9 : ℂ) * e6, by linear_combination ((1) : ℂ) * e0 + (191 / 6 : ℂ) * e1 + (-31 / 6 : ℂ) * e2 + (-46 / 9 : ℂ) * e4 + ((-3) : ℂ) * e5 + (-40 / 9 : ℂ) * e6, by linear_combination ((6) : ℂ) * e0 + (391 / 2 : ℂ) * e1 + (-63 / 2 : ℂ) * e2 + ((1) : ℂ) * e3 + (-92 / 3 : ℂ) * e4 + ((-19) : ℂ) * e5 + (-80 / 3 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 4, 5, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span12 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (3 / 40 : ℂ) * e0 + (11 / 8 : ℂ) * e1 + (-11 / 40 : ℂ) * e2 + (-9 / 40 : ℂ) * e3 + (-1 / 20 : ℂ) * e4 + (57 / 40 : ℂ) * e5 + (351 / 40 : ℂ) * e6, by linear_combination (-3 / 20 : ℂ) * e0 + (-1 / 4 : ℂ) * e1 + (1 / 20 : ℂ) * e2 + (9 / 20 : ℂ) * e3 + (1 / 10 : ℂ) * e4 + (-57 / 20 : ℂ) * e5 + (-351 / 20 : ℂ) * e6, by linear_combination (-1 / 40 : ℂ) * e0 + (3 / 8 : ℂ) * e1 + (-3 / 40 : ℂ) * e2 + (-17 / 40 : ℂ) * e3 + (-3 / 20 : ℂ) * e4 + (101 / 40 : ℂ) * e5 + (623 / 40 : ℂ) * e6, by linear_combination (-1 / 40 : ℂ) * e0 + (3 / 8 : ℂ) * e1 + (-3 / 40 : ℂ) * e2 + (23 / 40 : ℂ) * e3 + (-3 / 20 : ℂ) * e4 + (-139 / 40 : ℂ) * e5 + (-857 / 40 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 2, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span13 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (3 / 46 : ℂ) * e0 + (191 / 92 : ℂ) * e1 + (-31 / 92 : ℂ) * e2 + (-9 / 46 : ℂ) * e3 + (1 / 23 : ℂ) * e4 + (3 / 46 : ℂ) * e5 + (9 / 23 : ℂ) * e6, by linear_combination (-3 / 23 : ℂ) * e0 + (-38 / 23 : ℂ) * e1 + (4 / 23 : ℂ) * e2 + (9 / 23 : ℂ) * e3 + (-2 / 23 : ℂ) * e4 + (-3 / 23 : ℂ) * e5 + (-18 / 23 : ℂ) * e6, by linear_combination (-5 / 92 : ℂ) * e0 + (249 / 184 : ℂ) * e1 + (-25 / 184 : ℂ) * e2 + (-31 / 92 : ℂ) * e3 + (3 / 23 : ℂ) * e4 + (-5 / 92 : ℂ) * e5 + (-15 / 46 : ℂ) * e6, by linear_combination (-5 / 92 : ℂ) * e0 + (-579 / 184 : ℂ) * e1 + (67 / 184 : ℂ) * e2 + (61 / 92 : ℂ) * e3 + (3 / 23 : ℂ) * e4 + (-5 / 92 : ℂ) * e5 + (-15 / 46 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 3, 4, 5, 6, 7]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span14 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (1 / 3 : ℂ) * e4 + (1 / 3 : ℂ) * e6, by linear_combination (3 / 20 : ℂ) * e2 + (1 / 6 : ℂ) * e4 + (7 / 60 : ℂ) * e6, by linear_combination ((1) : ℂ) * e1 + (1 / 8 : ℂ) * e2 + (5 / 12 : ℂ) * e4 + (-1 / 2 : ℂ) * e5 + (13 / 24 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e1 + (-1 / 40 : ℂ) * e2 + (-5 / 12 : ℂ) * e4 + (1 / 2 : ℂ) * e5 + (-29 / 120 : ℂ) * e6, by linear_combination ((1) : ℂ) * e0 + ((6) : ℂ) * e1 + (31 / 20 : ℂ) * e2 + (7 / 2 : ℂ) * e4 + ((-3) : ℂ) * e5 + (73 / 20 : ℂ) * e6, by linear_combination ((6) : ℂ) * e0 + ((38) : ℂ) * e1 + (189 / 20 : ℂ) * e2 + ((1) : ℂ) * e3 + (131 / 6 : ℂ) * e4 + ((-19) : ℂ) * e5 + (1361 / 60 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 3, 4, 5, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span15 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (-10 / 39 : ℂ) * e0 + (-11 / 39 : ℂ) * e2 + (10 / 13 : ℂ) * e3 + (1 / 13 : ℂ) * e4 + (-190 / 39 : ℂ) * e5 + ((-30) : ℂ) * e6, by linear_combination (-7 / 78 : ℂ) * e0 + (2 / 39 : ℂ) * e2 + (7 / 26 : ℂ) * e3 + (1 / 13 : ℂ) * e4 + (-133 / 78 : ℂ) * e5 + (-21 / 2 : ℂ) * e6, by linear_combination (-3 / 26 : ℂ) * e0 + (-1 / 13 : ℂ) * e2 + (-2 / 13 : ℂ) * e3 + (-3 / 26 : ℂ) * e4 + (21 / 26 : ℂ) * e5 + ((5) : ℂ) * e6, by linear_combination (-3 / 26 : ℂ) * e0 + (-1 / 13 : ℂ) * e2 + (11 / 13 : ℂ) * e3 + (-3 / 26 : ℂ) * e4 + (-135 / 26 : ℂ) * e5 + ((-32) : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 3, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span16 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (-2 / 21 : ℂ) * e0 + (-4 / 7 : ℂ) * e1 + (-31 / 210 : ℂ) * e2 + (2 / 7 : ℂ) * e3 + (-1 / 70 : ℂ) * e4 + (-2 / 21 : ℂ) * e5 + (-4 / 7 : ℂ) * e6, by linear_combination (-1 / 21 : ℂ) * e0 + (-2 / 7 : ℂ) * e1 + (8 / 105 : ℂ) * e2 + (1 / 7 : ℂ) * e3 + (-2 / 35 : ℂ) * e4 + (-1 / 21 : ℂ) * e5 + (-2 / 7 : ℂ) * e6, by linear_combination (-5 / 42 : ℂ) * e0 + (2 / 7 : ℂ) * e1 + (-5 / 84 : ℂ) * e2 + (-1 / 7 : ℂ) * e3 + (3 / 28 : ℂ) * e4 + (-5 / 42 : ℂ) * e5 + (-5 / 7 : ℂ) * e6, by linear_combination (5 / 42 : ℂ) * e0 + (-2 / 7 : ℂ) * e1 + (67 / 420 : ℂ) * e2 + (1 / 7 : ℂ) * e3 + (27 / 140 : ℂ) * e4 + (5 / 42 : ℂ) * e5 + (5 / 7 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 4, 5, 6, 7, 8]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span17 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (1 / 3 : ℂ) * e3 + (1 / 3 : ℂ) * e5, by linear_combination (-111 / 1165 : ℂ) * e0 + (-702 / 1165 : ℂ) * e1 + (-18 / 1165 : ℂ) * e2 + (-628 / 3495 : ℂ) * e3 + (351 / 1165 : ℂ) * e4 + (-170 / 699 : ℂ) * e5 + (-3 / 1165 : ℂ) * e6, by linear_combination (-37 / 466 : ℂ) * e0 + (116 / 233 : ℂ) * e1 + (-3 / 233 : ℂ) * e2 + (179 / 1398 : ℂ) * e3 + (-58 / 233 : ℂ) * e4 + (169 / 699 : ℂ) * e5 + (-1 / 466 : ℂ) * e6, by linear_combination (37 / 2330 : ℂ) * e0 + (-1048 / 1165 : ℂ) * e1 + (3 / 1165 : ℂ) * e2 + (-2509 / 6990 : ℂ) * e3 + (524 / 1165 : ℂ) * e4 + (-127 / 699 : ℂ) * e5 + (1 / 2330 : ℂ) * e6, by linear_combination (18 / 1165 : ℂ) * e0 + (-264 / 1165 : ℂ) * e1 + (-186 / 1165 : ℂ) * e2 + (-92 / 1165 : ℂ) * e3 + (132 / 1165 : ℂ) * e4 + (-16 / 233 : ℂ) * e5 + (-31 / 1165 : ℂ) * e6, by linear_combination (-3 / 1165 : ℂ) * e0 + (44 / 1165 : ℂ) * e1 + (31 / 1165 : ℂ) * e2 + (46 / 3495 : ℂ) * e3 + (-22 / 1165 : ℂ) * e4 + (8 / 699 : ℂ) * e5 + (-189 / 1165 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 4, 5, 6, 7, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span18 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (1 / 3 : ℂ) * e3 + (1 / 3 : ℂ) * e5, by linear_combination (-2 / 21 : ℂ) * e0 + (-38 / 63 : ℂ) * e1 + (-1 / 63 : ℂ) * e2 + (-34 / 189 : ℂ) * e3 + (19 / 63 : ℂ) * e4 + (-46 / 189 : ℂ) * e5 + (1 / 63 : ℂ) * e6, by linear_combination (-5 / 63 : ℂ) * e0 + (94 / 189 : ℂ) * e1 + (-5 / 378 : ℂ) * e2 + (145 / 1134 : ℂ) * e3 + (-47 / 189 : ℂ) * e4 + (137 / 567 : ℂ) * e5 + (5 / 378 : ℂ) * e6, by linear_combination (1 / 63 : ℂ) * e0 + (-170 / 189 : ℂ) * e1 + (1 / 378 : ℂ) * e2 + (-407 / 1134 : ℂ) * e3 + (85 / 189 : ℂ) * e4 + (-103 / 567 : ℂ) * e5 + (-1 / 378 : ℂ) * e6, by linear_combination (1 / 63 : ℂ) * e0 + (-44 / 189 : ℂ) * e1 + (-31 / 189 : ℂ) * e2 + (-46 / 567 : ℂ) * e3 + (22 / 189 : ℂ) * e4 + (-40 / 567 : ℂ) * e5 + (31 / 189 : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 4, 5, 6, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span19 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (3 / 40 : ℂ) * e0 + (-11 / 10 : ℂ) * e1 + (-31 / 40 : ℂ) * e2 + (-1 / 20 : ℂ) * e3 + (11 / 20 : ℂ) * e4 + (189 / 40 : ℂ) * e5 + (233 / 8 : ℂ) * e6, by linear_combination (-3 / 20 : ℂ) * e0 + (1 / 5 : ℂ) * e1 + (11 / 20 : ℂ) * e2 + (1 / 10 : ℂ) * e3 + (-1 / 10 : ℂ) * e4 + (-69 / 20 : ℂ) * e5 + (-85 / 4 : ℂ) * e6, by linear_combination (-1 / 40 : ℂ) * e0 + (-3 / 10 : ℂ) * e1 + (-23 / 40 : ℂ) * e2 + (-3 / 20 : ℂ) * e3 + (3 / 20 : ℂ) * e4 + (137 / 40 : ℂ) * e5 + (169 / 8 : ℂ) * e6, by linear_combination (-1 / 40 : ℂ) * e0 + (-3 / 10 : ℂ) * e1 + (17 / 40 : ℂ) * e2 + (-3 / 20 : ℂ) * e3 + (3 / 20 : ℂ) * e4 + (-103 / 40 : ℂ) * e5 + (-127 / 8 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 4, 5, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span20 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (1 / 3 : ℂ) * e3 + (1 / 3 : ℂ) * e4, by linear_combination (-3 / 22 : ℂ) * e0 + (9 / 22 : ℂ) * e2 + (1 / 33 : ℂ) * e3 + (-2 / 33 : ℂ) * e4 + (-57 / 22 : ℂ) * e5 + (-351 / 22 : ℂ) * e6, by linear_combination (-1 / 22 : ℂ) * e0 + (-4 / 11 : ℂ) * e2 + (-1 / 22 : ℂ) * e3 + (1 / 11 : ℂ) * e4 + (47 / 22 : ℂ) * e5 + (145 / 11 : ℂ) * e6, by linear_combination (-1 / 22 : ℂ) * e0 + (7 / 11 : ℂ) * e2 + (-1 / 22 : ℂ) * e3 + (1 / 11 : ℂ) * e4 + (-85 / 22 : ℂ) * e5 + (-262 / 11 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 4, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span21 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (3 / 46 : ℂ) * e0 + (-22 / 23 : ℂ) * e1 + (-31 / 46 : ℂ) * e2 + (11 / 23 : ℂ) * e3 + (1 / 23 : ℂ) * e4 + (189 / 46 : ℂ) * e5 + (1165 / 46 : ℂ) * e6, by linear_combination (-3 / 23 : ℂ) * e0 + (-2 / 23 : ℂ) * e1 + (8 / 23 : ℂ) * e2 + (1 / 23 : ℂ) * e3 + (-2 / 23 : ℂ) * e4 + (-51 / 23 : ℂ) * e5 + (-314 / 23 : ℂ) * e6, by linear_combination (-5 / 92 : ℂ) * e0 + (3 / 23 : ℂ) * e1 + (-25 / 92 : ℂ) * e2 + (-3 / 46 : ℂ) * e3 + (3 / 23 : ℂ) * e4 + (145 / 92 : ℂ) * e5 + (895 / 92 : ℂ) * e6, by linear_combination (-5 / 92 : ℂ) * e0 + (3 / 23 : ℂ) * e1 + (67 / 92 : ℂ) * e2 + (-3 / 46 : ℂ) * e3 + (3 / 23 : ℂ) * e4 + (-407 / 92 : ℂ) * e5 + (-2509 / 92 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 1, 5, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span22 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e1, by linear_combination (1 / 3 : ℂ) * e2 + (1 / 3 : ℂ) * e4, by linear_combination (-3 / 31 : ℂ) * e0 + (-18 / 31 : ℂ) * e1 + (-16 / 93 : ℂ) * e2 + (9 / 31 : ℂ) * e3 + (-22 / 93 : ℂ) * e4 + (-3 / 31 : ℂ) * e5 + (-18 / 31 : ℂ) * e6, by linear_combination (-5 / 62 : ℂ) * e0 + (16 / 31 : ℂ) * e1 + (25 / 186 : ℂ) * e2 + (-8 / 31 : ℂ) * e3 + (23 / 93 : ℂ) * e4 + (-5 / 62 : ℂ) * e5 + (-15 / 31 : ℂ) * e6, by linear_combination (1 / 62 : ℂ) * e0 + (-28 / 31 : ℂ) * e1 + (-67 / 186 : ℂ) * e2 + (14 / 31 : ℂ) * e3 + (-17 / 93 : ℂ) * e4 + (1 / 62 : ℂ) * e5 + (3 / 31 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 2, 3, 4, 5, 6, 7]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span23 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 5 : ℂ) * e1 + (3 / 50 : ℂ) * e2 + (1 / 3 : ℂ) * e4 + (47 / 150 : ℂ) * e6, by linear_combination (1 / 3 : ℂ) * e4 + (1 / 3 : ℂ) * e6, by linear_combination (3 / 20 : ℂ) * e2 + (1 / 6 : ℂ) * e4 + (7 / 60 : ℂ) * e6, by linear_combination (1 / 5 : ℂ) * e1 + (37 / 200 : ℂ) * e2 + (3 / 4 : ℂ) * e4 + (-1 / 2 : ℂ) * e5 + (171 / 200 : ℂ) * e6, by linear_combination (-1 / 5 : ℂ) * e1 + (-17 / 200 : ℂ) * e2 + (-3 / 4 : ℂ) * e4 + (1 / 2 : ℂ) * e5 + (-111 / 200 : ℂ) * e6, by linear_combination ((1) : ℂ) * e0 + (6 / 5 : ℂ) * e1 + (191 / 100 : ℂ) * e2 + (11 / 2 : ℂ) * e4 + ((-3) : ℂ) * e5 + (553 / 100 : ℂ) * e6, by linear_combination ((6) : ℂ) * e0 + (38 / 5 : ℂ) * e1 + (1173 / 100 : ℂ) * e2 + ((1) : ℂ) * e3 + (69 / 2 : ℂ) * e4 + ((-19) : ℂ) * e5 + (3459 / 100 : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 2, 3, 4, 5, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span24 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (-47 / 195 : ℂ) * e0 + (1 / 5 : ℂ) * e1 + (-8 / 39 : ℂ) * e2 + (47 / 65 : ℂ) * e3 + (6 / 65 : ℂ) * e4 + (-893 / 195 : ℂ) * e5 + (-141 / 5 : ℂ) * e6, by linear_combination (-10 / 39 : ℂ) * e0 + (-11 / 39 : ℂ) * e2 + (10 / 13 : ℂ) * e3 + (1 / 13 : ℂ) * e4 + (-190 / 39 : ℂ) * e5 + ((-30) : ℂ) * e6, by linear_combination (-7 / 78 : ℂ) * e0 + (2 / 39 : ℂ) * e2 + (7 / 26 : ℂ) * e3 + (1 / 13 : ℂ) * e4 + (-133 / 78 : ℂ) * e5 + (-21 / 2 : ℂ) * e6, by linear_combination (-3 / 26 : ℂ) * e0 + (-1 / 13 : ℂ) * e2 + (-2 / 13 : ℂ) * e3 + (-3 / 26 : ℂ) * e4 + (21 / 26 : ℂ) * e5 + ((5) : ℂ) * e6, by linear_combination (-3 / 26 : ℂ) * e0 + (-1 / 13 : ℂ) * e2 + (11 / 13 : ℂ) * e3 + (-3 / 26 : ℂ) * e4 + (-135 / 26 : ℂ) * e5 + ((-32) : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 2, 3, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span25 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (-2 / 33 : ℂ) * e0 + (7 / 55 : ℂ) * e1 + (-46 / 825 : ℂ) * e2 + (2 / 11 : ℂ) * e3 + (-6 / 275 : ℂ) * e4 + (-2 / 33 : ℂ) * e5 + (-4 / 11 : ℂ) * e6, by linear_combination (-2 / 33 : ℂ) * e0 + (-4 / 55 : ℂ) * e1 + (-191 / 1650 : ℂ) * e2 + (2 / 11 : ℂ) * e3 + (-1 / 550 : ℂ) * e4 + (-2 / 33 : ℂ) * e5 + (-4 / 11 : ℂ) * e6, by linear_combination (-1 / 33 : ℂ) * e0 + (-2 / 55 : ℂ) * e1 + (76 / 825 : ℂ) * e2 + (1 / 11 : ℂ) * e3 + (-14 / 275 : ℂ) * e4 + (-1 / 33 : ℂ) * e5 + (-2 / 11 : ℂ) * e6, by linear_combination (-3 / 22 : ℂ) * e0 + (2 / 55 : ℂ) * e1 + (-83 / 1100 : ℂ) * e2 + (-1 / 11 : ℂ) * e3 + (111 / 1100 : ℂ) * e4 + (-3 / 22 : ℂ) * e5 + (-9 / 11 : ℂ) * e6, by linear_combination (3 / 22 : ℂ) * e0 + (-2 / 55 : ℂ) * e1 + (193 / 1100 : ℂ) * e2 + (1 / 11 : ℂ) * e3 + (219 / 1100 : ℂ) * e4 + (3 / 22 : ℂ) * e5 + (9 / 11 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [0, 4, 5, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span26 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (3 / 44 : ℂ) * e0 + (-31 / 44 : ℂ) * e1 + (-23 / 66 : ℂ) * e2 + (1 / 2 : ℂ) * e3 + (-10 / 33 : ℂ) * e4 + (189 / 44 : ℂ) * e5 + (1165 / 44 : ℂ) * e6, by linear_combination (1 / 3 : ℂ) * e2 + (1 / 3 : ℂ) * e4, by linear_combination (-3 / 22 : ℂ) * e0 + (9 / 22 : ℂ) * e1 + (1 / 33 : ℂ) * e2 + (-2 / 33 : ℂ) * e4 + (-57 / 22 : ℂ) * e5 + (-351 / 22 : ℂ) * e6, by linear_combination (-1 / 22 : ℂ) * e0 + (-4 / 11 : ℂ) * e1 + (-1 / 22 : ℂ) * e2 + (1 / 11 : ℂ) * e4 + (47 / 22 : ℂ) * e5 + (145 / 11 : ℂ) * e6, by linear_combination (-1 / 22 : ℂ) * e0 + (7 / 11 : ℂ) * e1 + (-1 / 22 : ℂ) * e2 + (1 / 11 : ℂ) * e4 + (-85 / 22 : ℂ) * e5 + (-262 / 11 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [1, 2, 3, 4, 5, 6, 8]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span27 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e0, by linear_combination (50 / 47 : ℂ) * e0 + (-10 / 47 : ℂ) * e1 + (-3 / 47 : ℂ) * e2 + (-1 / 47 : ℂ) * e4, by linear_combination (35 / 94 : ℂ) * e0 + (-7 / 94 : ℂ) * e1 + (6 / 47 : ℂ) * e2 + (2 / 47 : ℂ) * e4, by linear_combination (513 / 188 : ℂ) * e0 + (-65 / 188 : ℂ) * e1 + (1 / 47 : ℂ) * e2 + (-15 / 94 : ℂ) * e4 + (-1 / 2 : ℂ) * e5, by linear_combination (-333 / 188 : ℂ) * e0 + (29 / 188 : ℂ) * e1 + (1 / 47 : ℂ) * e2 + (-15 / 94 : ℂ) * e4 + (1 / 2 : ℂ) * e5, by linear_combination (-27 / 37 : ℂ) * e0 + (3 / 37 : ℂ) * e1 + (-6 / 37 : ℂ) * e3 + (6 / 37 : ℂ) * e5 + (-1 / 37 : ℂ) * e6, by linear_combination (9 / 74 : ℂ) * e0 + (-1 / 74 : ℂ) * e1 + (1 / 37 : ℂ) * e3 + (-1 / 37 : ℂ) * e5 + (-6 / 37 : ℂ) * e6⟩

/-- Spanning certificate for the index set [1, 2, 3, 4, 5, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span28 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e0, by linear_combination (50 / 47 : ℂ) * e0 + (-10 / 47 : ℂ) * e1 + (-3 / 47 : ℂ) * e2 + (-1 / 47 : ℂ) * e4, by linear_combination (35 / 94 : ℂ) * e0 + (-7 / 94 : ℂ) * e1 + (6 / 47 : ℂ) * e2 + (2 / 47 : ℂ) * e4, by linear_combination (45 / 94 : ℂ) * e0 + (-9 / 94 : ℂ) * e1 + (1 / 47 : ℂ) * e2 + (-1 / 2 : ℂ) * e3 + (-15 / 94 : ℂ) * e4 + ((3) : ℂ) * e5 + (37 / 2 : ℂ) * e6, by linear_combination (45 / 94 : ℂ) * e0 + (-9 / 94 : ℂ) * e1 + (1 / 47 : ℂ) * e2 + (1 / 2 : ℂ) * e3 + (-15 / 94 : ℂ) * e4 + ((-3) : ℂ) * e5 + (-37 / 2 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [1, 2, 3, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span29 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e0, by linear_combination ((1) : ℂ) * e0 + (-1 / 5 : ℂ) * e1 + (-3 / 50 : ℂ) * e2 + (1 / 50 : ℂ) * e4, by linear_combination (1 / 2 : ℂ) * e0 + (-1 / 10 : ℂ) * e1 + (3 / 25 : ℂ) * e2 + (-1 / 25 : ℂ) * e4, by linear_combination (9 / 4 : ℂ) * e0 + (-1 / 4 : ℂ) * e1 + (1 / 20 : ℂ) * e2 + (-1 / 2 : ℂ) * e3 + (3 / 20 : ℂ) * e4, by linear_combination (-9 / 4 : ℂ) * e0 + (1 / 4 : ℂ) * e1 + (1 / 20 : ℂ) * e2 + (1 / 2 : ℂ) * e3 + (3 / 20 : ℂ) * e4, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [1, 4, 5, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span30 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination ((1) : ℂ) * e0, by linear_combination (1 / 3 : ℂ) * e2 + (1 / 3 : ℂ) * e4, by linear_combination ((-2) : ℂ) * e0 + ((-1) : ℂ) * e1 + (-2 / 3 : ℂ) * e2 + ((1) : ℂ) * e3 + (-2 / 3 : ℂ) * e4 + ((6) : ℂ) * e5 + ((37) : ℂ) * e6, by linear_combination (-2 / 3 : ℂ) * e0 + (-5 / 6 : ℂ) * e1 + (-5 / 18 : ℂ) * e2 + (1 / 3 : ℂ) * e3 + (-1 / 9 : ℂ) * e4 + ((5) : ℂ) * e5 + (185 / 6 : ℂ) * e6, by linear_combination (-2 / 3 : ℂ) * e0 + (1 / 6 : ℂ) * e1 + (-5 / 18 : ℂ) * e2 + (1 / 3 : ℂ) * e3 + (-1 / 9 : ℂ) * e4 + ((-1) : ℂ) * e5 + (-37 / 6 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 3, 4, 5, 6, 7, 8]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span31 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 5 : ℂ) * e0 + (3 / 50 : ℂ) * e1 + (1 / 3 : ℂ) * e3 + (47 / 150 : ℂ) * e5, by linear_combination (1 / 3 : ℂ) * e3 + (1 / 3 : ℂ) * e5, by linear_combination (3 / 20 : ℂ) * e1 + (1 / 6 : ℂ) * e3 + (7 / 60 : ℂ) * e5, by linear_combination (1 / 5 : ℂ) * e0 + (37 / 200 : ℂ) * e1 + (3 / 4 : ℂ) * e3 + (-1 / 2 : ℂ) * e4 + (171 / 200 : ℂ) * e5, by linear_combination (-1 / 5 : ℂ) * e0 + (-17 / 200 : ℂ) * e1 + (-3 / 4 : ℂ) * e3 + (1 / 2 : ℂ) * e4 + (-111 / 200 : ℂ) * e5, by linear_combination (-12 / 185 : ℂ) * e0 + (-81 / 1850 : ℂ) * e1 + (-6 / 37 : ℂ) * e2 + (-9 / 37 : ℂ) * e3 + (6 / 37 : ℂ) * e4 + (-423 / 1850 : ℂ) * e5 + (-1 / 37 : ℂ) * e6, by linear_combination (2 / 185 : ℂ) * e0 + (27 / 3700 : ℂ) * e1 + (1 / 37 : ℂ) * e2 + (3 / 74 : ℂ) * e3 + (-1 / 37 : ℂ) * e4 + (141 / 3700 : ℂ) * e5 + (-6 / 37 : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 3, 4, 5, 6, 7, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span32 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 5 : ℂ) * e0 + (3 / 50 : ℂ) * e1 + (1 / 3 : ℂ) * e3 + (47 / 150 : ℂ) * e5, by linear_combination (1 / 3 : ℂ) * e3 + (1 / 3 : ℂ) * e5, by linear_combination (3 / 20 : ℂ) * e1 + (1 / 6 : ℂ) * e3 + (7 / 60 : ℂ) * e5, by linear_combination (1 / 5 : ℂ) * e0 + (37 / 200 : ℂ) * e1 + (3 / 4 : ℂ) * e3 + (-1 / 2 : ℂ) * e4 + (171 / 200 : ℂ) * e5, by linear_combination (-1 / 5 : ℂ) * e0 + (-17 / 200 : ℂ) * e1 + (-3 / 4 : ℂ) * e3 + (1 / 2 : ℂ) * e4 + (-111 / 200 : ℂ) * e5, by linear_combination (-1 / 15 : ℂ) * e0 + (-9 / 200 : ℂ) * e1 + (-1 / 6 : ℂ) * e2 + (-1 / 4 : ℂ) * e3 + (1 / 6 : ℂ) * e4 + (-47 / 200 : ℂ) * e5 + (1 / 6 : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 3, 4, 5, 6, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span33 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 9 : ℂ) * e0 + (-2 / 9 : ℂ) * e2 + (2 / 9 : ℂ) * e4 + (4 / 3 : ℂ) * e5 + (74 / 9 : ℂ) * e6, by linear_combination (-40 / 423 : ℂ) * e0 + (-3 / 47 : ℂ) * e1 + (-100 / 423 : ℂ) * e2 + (-1 / 47 : ℂ) * e3 + (100 / 423 : ℂ) * e4 + (200 / 141 : ℂ) * e5 + (3700 / 423 : ℂ) * e6, by linear_combination (-14 / 423 : ℂ) * e0 + (6 / 47 : ℂ) * e1 + (-35 / 423 : ℂ) * e2 + (2 / 47 : ℂ) * e3 + (35 / 423 : ℂ) * e4 + (70 / 141 : ℂ) * e5 + (1295 / 423 : ℂ) * e6, by linear_combination (-2 / 47 : ℂ) * e0 + (1 / 47 : ℂ) * e1 + (-57 / 94 : ℂ) * e2 + (-15 / 94 : ℂ) * e3 + (5 / 47 : ℂ) * e4 + (171 / 47 : ℂ) * e5 + (2109 / 94 : ℂ) * e6, by linear_combination (-2 / 47 : ℂ) * e0 + (1 / 47 : ℂ) * e1 + (37 / 94 : ℂ) * e2 + (-15 / 94 : ℂ) * e3 + (5 / 47 : ℂ) * e4 + (-111 / 47 : ℂ) * e5 + (-1369 / 94 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 3, 4, 5, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span34 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 5 : ℂ) * e0 + (3 / 50 : ℂ) * e1 + (1 / 3 : ℂ) * e3 + (47 / 150 : ℂ) * e4, by linear_combination (1 / 3 : ℂ) * e3 + (1 / 3 : ℂ) * e4, by linear_combination (3 / 20 : ℂ) * e1 + (1 / 6 : ℂ) * e3 + (7 / 60 : ℂ) * e4, by linear_combination (1 / 20 : ℂ) * e1 + (-1 / 2 : ℂ) * e2 + (3 / 20 : ℂ) * e4 + ((3) : ℂ) * e5 + (37 / 2 : ℂ) * e6, by linear_combination (1 / 20 : ℂ) * e1 + (1 / 2 : ℂ) * e2 + (3 / 20 : ℂ) * e4 + ((-3) : ℂ) * e5 + (-37 / 2 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 3, 4, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span35 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 9 : ℂ) * e0 + (-2 / 9 : ℂ) * e2 + (2 / 9 : ℂ) * e3 + (4 / 3 : ℂ) * e5 + (74 / 9 : ℂ) * e6, by linear_combination (-4 / 45 : ℂ) * e0 + (-3 / 50 : ℂ) * e1 + (-2 / 9 : ℂ) * e2 + (2 / 9 : ℂ) * e3 + (1 / 50 : ℂ) * e4 + (4 / 3 : ℂ) * e5 + (74 / 9 : ℂ) * e6, by linear_combination (-2 / 45 : ℂ) * e0 + (3 / 25 : ℂ) * e1 + (-1 / 9 : ℂ) * e2 + (1 / 9 : ℂ) * e3 + (-1 / 25 : ℂ) * e4 + (2 / 3 : ℂ) * e5 + (37 / 9 : ℂ) * e6, by linear_combination (1 / 20 : ℂ) * e1 + (-1 / 2 : ℂ) * e2 + (3 / 20 : ℂ) * e4 + ((3) : ℂ) * e5 + (37 / 2 : ℂ) * e6, by linear_combination (1 / 20 : ℂ) * e1 + (1 / 2 : ℂ) * e2 + (3 / 20 : ℂ) * e4 + ((-3) : ℂ) * e5 + (-37 / 2 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 3, 5, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span36 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 5 : ℂ) * e0 + (3 / 50 : ℂ) * e1 + (1 / 3 : ℂ) * e2 + (47 / 150 : ℂ) * e4, by linear_combination (1 / 3 : ℂ) * e2 + (1 / 3 : ℂ) * e4, by linear_combination (3 / 20 : ℂ) * e1 + (1 / 6 : ℂ) * e2 + (7 / 60 : ℂ) * e4, by linear_combination (1 / 5 : ℂ) * e0 + (37 / 200 : ℂ) * e1 + (3 / 4 : ℂ) * e2 + (-1 / 2 : ℂ) * e3 + (171 / 200 : ℂ) * e4, by linear_combination (-1 / 5 : ℂ) * e0 + (-17 / 200 : ℂ) * e1 + (-3 / 4 : ℂ) * e2 + (1 / 2 : ℂ) * e3 + (-111 / 200 : ℂ) * e4, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [2, 4, 5, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span37 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (1 / 9 : ℂ) * e0 + (-2 / 9 : ℂ) * e1 + (2 / 9 : ℂ) * e3 + (4 / 3 : ℂ) * e5 + (74 / 9 : ℂ) * e6, by linear_combination (1 / 3 : ℂ) * e2 + (1 / 3 : ℂ) * e4, by linear_combination (-2 / 9 : ℂ) * e0 + (-5 / 9 : ℂ) * e1 + (-2 / 3 : ℂ) * e2 + (5 / 9 : ℂ) * e3 + (-2 / 3 : ℂ) * e4 + (10 / 3 : ℂ) * e5 + (185 / 9 : ℂ) * e6, by linear_combination (-2 / 27 : ℂ) * e0 + (-37 / 54 : ℂ) * e1 + (-5 / 18 : ℂ) * e2 + (5 / 27 : ℂ) * e3 + (-1 / 9 : ℂ) * e4 + (37 / 9 : ℂ) * e5 + (1369 / 54 : ℂ) * e6, by linear_combination (-2 / 27 : ℂ) * e0 + (17 / 54 : ℂ) * e1 + (-5 / 18 : ℂ) * e2 + (5 / 27 : ℂ) * e3 + (-1 / 9 : ℂ) * e4 + (-17 / 9 : ℂ) * e5 + (-629 / 54 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩

/-- Spanning certificate for the index set [3, 4, 5, 6, 7, 8, 9]: the seven `z` rows are
linearly independent, and the inverse of that 7x7 matrix is supplied inline. -/
theorem span38 {c0 c1 c2 c3 c4 c5 c6 : ℂ} (e0 : (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e1 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) (e2 : (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e3 : (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e4 : (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0) (e5 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0) (e6 : (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 := by
  refine ⟨by linear_combination (-3 / 40 : ℂ) * e0 + (-1 / 2 : ℂ) * e1 + (-5 / 12 : ℂ) * e2 + (1 / 2 : ℂ) * e3 + (-47 / 120 : ℂ) * e4 + ((3) : ℂ) * e5 + (37 / 2 : ℂ) * e6, by linear_combination (1 / 3 : ℂ) * e2 + (1 / 3 : ℂ) * e4, by linear_combination (3 / 20 : ℂ) * e0 + (1 / 6 : ℂ) * e2 + (7 / 60 : ℂ) * e4, by linear_combination (1 / 20 : ℂ) * e0 + (-1 / 2 : ℂ) * e1 + (3 / 20 : ℂ) * e4 + ((3) : ℂ) * e5 + (37 / 2 : ℂ) * e6, by linear_combination (1 / 20 : ℂ) * e0 + (1 / 2 : ℂ) * e1 + (3 / 20 : ℂ) * e4 + ((-3) : ℂ) * e5 + (-37 / 2 : ℂ) * e6, by linear_combination ((-1) : ℂ) * e5 + ((-6) : ℂ) * e6, by linear_combination ((1) : ℂ) * e6⟩


set_option maxHeartbeats 1000000 in
theorem proof :
  ∃ u : Fin 10 → Fin 2 → ℂ, ∃ w : Fin 10 → Fin 2 → ℂ, ∃ z : Fin 10 → Fin 7 → ℂ,
    (∀ i, u i ≠ 0) ∧
    (∀ i, w i ≠ 0) ∧
    (∀ i, z i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∑ r, star (u i r) * u j r) *
      (∑ r, star (w i r) * w j r) *
      (∑ r, star (z i r) * z j r) = 0) ∧
    (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 → ∀ c : Fin 7 → ℂ, c ≠ 0 →
      ∃ i,
        (∑ r, star (u i r) * a r) *
        (∑ r, star (w i r) * b r) *
        (∑ r, star (z i r) * c r) ≠ 0) := by
  refine ⟨![![1, 0],
     ![1, 0],
     ![0, 1],
     ![0, 1],
     ![1, 1],
     ![1, 1],
     ![1, (-1)],
     ![1, (-1)],
     ![1, 2],
     ![2, (-1)]],
    ![![1, 1],
     ![1, 3],
     ![1, 4],
     ![1, 5],
     ![1, 2],
     ![(-4), 1],
     ![(-3), 1],
     ![(-5), 1],
     ![(-1), 1],
     ![(-2), 1]],
    ![![0, 0, (-6), (-5), 1, 1, 0],
     ![1, 0, 0, 0, 0, 0, 0],
     ![5, (-4), (-2), 0, 0, 0, 0],
     ![0, (-3), 6, 1, 1, 0, 0],
     ![0, 0, 0, (-1), 1, (-6), 1],
     ![0, 2, 2, (-3), (-3), 0, 0],
     ![2, 2, 1, (-1), 1, 0, 0],
     ![0, 1, (-2), 3, 3, 0, 0],
     ![0, 0, 0, 0, 0, (-1), (-6)],
     ![0, 0, 0, 0, 0, 0, 1]],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((2) : ℂ) ≠ 0; norm_num⟩
  · intro i
    fin_cases i
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((-4) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((-3) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((-5) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((-1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((-2) : ℂ) ≠ 0; norm_num⟩
  · intro i
    fin_cases i
    · rw [Function.ne_iff]; exact ⟨2, by show ((-6) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((5) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show ((-3) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨3, by show ((-1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show ((2) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨0, by show ((2) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨1, by show ((1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨5, by show ((-1) : ℂ) ≠ 0; norm_num⟩
    · rw [Function.ne_iff]; exact ⟨6, by show ((1) : ℂ) ≠ 0; norm_num⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | norm_num [Fin.sum_univ_succ, Complex.conj_ofNat, Complex.conj_natCast]
  · intro a ha b hb c hc
    by_contra hcon
    push_neg at hcon
    obtain ⟨a0, a1, rfl⟩ : ∃ x y : ℂ, a = ![x, y] :=
      ⟨a 0, a 1, by funext i; fin_cases i <;> rfl⟩
    obtain ⟨b0, b1, rfl⟩ : ∃ x y : ℂ, b = ![x, y] :=
      ⟨b 0, b 1, by funext i; fin_cases i <;> rfl⟩
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, rfl⟩ :
        ∃ x0 x1 x2 x3 x4 x5 x6 : ℂ, c = ![x0, x1, x2, x3, x4, x5, x6] :=
      ⟨c 0, c 1, c 2, c 3, c 4, c 5, c 6, by funext i; fin_cases i <;> rfl⟩
    have E0 : (((1) : ℂ) * a0 + ((0) : ℂ) * a1) * (((1) : ℂ) * b0 + ((1) : ℂ) * b1) * (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((-6) : ℂ) * c2 + ((-5) : ℂ) * c3 + ((1) : ℂ) * c4 + ((1) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 0
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E1 : (((1) : ℂ) * a0 + ((0) : ℂ) * a1) * (((1) : ℂ) * b0 + ((3) : ℂ) * b1) * (((1) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 1
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E2 : (((0) : ℂ) * a0 + ((1) : ℂ) * a1) * (((1) : ℂ) * b0 + ((4) : ℂ) * b1) * (((5) : ℂ) * c0 + ((-4) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 2
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E3 : (((0) : ℂ) * a0 + ((1) : ℂ) * a1) * (((1) : ℂ) * b0 + ((5) : ℂ) * b1) * (((0) : ℂ) * c0 + ((-3) : ℂ) * c1 + ((6) : ℂ) * c2 + ((1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 3
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E4 : (((1) : ℂ) * a0 + ((1) : ℂ) * a1) * (((1) : ℂ) * b0 + ((2) : ℂ) * b1) * (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((-6) : ℂ) * c5 + ((1) : ℂ) * c6) = 0 := by
      have h := hcon 4
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E5 : (((1) : ℂ) * a0 + ((1) : ℂ) * a1) * (((-4) : ℂ) * b0 + ((1) : ℂ) * b1) * (((0) : ℂ) * c0 + ((2) : ℂ) * c1 + ((2) : ℂ) * c2 + ((-3) : ℂ) * c3 + ((-3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 5
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E6 : (((1) : ℂ) * a0 + ((-1) : ℂ) * a1) * (((-3) : ℂ) * b0 + ((1) : ℂ) * b1) * (((2) : ℂ) * c0 + ((2) : ℂ) * c1 + ((1) : ℂ) * c2 + ((-1) : ℂ) * c3 + ((1) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 6
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E7 : (((1) : ℂ) * a0 + ((-1) : ℂ) * a1) * (((-5) : ℂ) * b0 + ((1) : ℂ) * b1) * (((0) : ℂ) * c0 + ((1) : ℂ) * c1 + ((-2) : ℂ) * c2 + ((3) : ℂ) * c3 + ((3) : ℂ) * c4 + ((0) : ℂ) * c5 + ((0) : ℂ) * c6) = 0 := by
      have h := hcon 7
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E8 : (((1) : ℂ) * a0 + ((2) : ℂ) * a1) * (((-1) : ℂ) * b0 + ((1) : ℂ) * b1) * (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((-1) : ℂ) * c5 + ((-6) : ℂ) * c6) = 0 := by
      have h := hcon 8
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have E9 : (((2) : ℂ) * a0 + ((-1) : ℂ) * a1) * (((-2) : ℂ) * b0 + ((1) : ℂ) * b1) * (((0) : ℂ) * c0 + ((0) : ℂ) * c1 + ((0) : ℂ) * c2 + ((0) : ℂ) * c3 + ((0) : ℂ) * c4 + ((0) : ℂ) * c5 + ((1) : ℂ) * c6) = 0 := by
      have h := hcon 9
      simp [Fin.sum_univ_succ, Complex.star_def, Complex.conj_ofNat, Complex.conj_natCast, -mul_eq_zero] at h
      linear_combination h
    have akill : ∀ p q r s : ℂ, p * s - q * r ≠ 0 →
        p * a0 + q * a1 = 0 → r * a0 + s * a1 = 0 → False := by
      intro p q r s hd h1 h2
      obtain ⟨k0, k1⟩ := pair2 hd h1 h2
      subst k0; subst k1
      exact ha (by funext i; fin_cases i <;> rfl)
    have bkill : ∀ p q r s : ℂ, p * s - q * r ≠ 0 →
        p * b0 + q * b1 = 0 → r * b0 + s * b1 = 0 → False := by
      intro p q r s hd h1 h2
      obtain ⟨k0, k1⟩ := pair2 hd h1 h2
      subst k0; subst k1
      exact hb (by funext i; fin_cases i <;> rfl)
    have hzero : c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 → False := by
      rintro ⟨k0, k1, k2, k3, k4, k5, k6⟩
      subst k0; subst k1; subst k2; subst k3; subst k4; subst k5; subst k6
      exact hc (by funext i; fin_cases i <;> rfl)
    by_cases pA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 = 0
    ·
      by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
      ·
        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
        have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
        have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB0 h
        have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB0 h
        have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB0 h
        have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
        have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
        have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
        have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
        exact hzero (span31 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
      ·
        by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
        ·
          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB1 h
          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB1 h
          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB1 h
          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
          have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
          exact hzero (span31 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
        ·
          by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
          ·
            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
            have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
            have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB2 h
            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB2 h
            have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
            have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
            have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
            exact hzero (span38 (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
          ·
            by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
            ·
              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
              have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
              have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB3 h
              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
              have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
              have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
              have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
              exact hzero (span37 (killz nA1 nB2 E2) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
            ·
              by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
              ·
                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
                have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                exact hzero (span36 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
              ·
                by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                ·
                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                  have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
                  have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                  have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                  have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                  have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                  exact hzero (span35 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                ·
                  by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                  ·
                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                    have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
                    have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                    have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                    have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                    have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                    exact hzero (span34 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                  ·
                    by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                    ·
                      have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                      have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                      have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                      have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
                      have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                      have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                      have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                      have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                      have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                      have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                      have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                      have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                      exact hzero (span33 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                    ·
                      by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                      ·
                        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                        have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                        have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                        have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                        have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                        have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                        have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                        have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                        have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB8 h
                        exact hzero (span32 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA5 nB9 E9))
                      ·
                        by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                        ·
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                          have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                          exact hzero (span31 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
                        ·
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((0) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA0 h
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA0 h
                          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA0 h
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                          have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                          exact hzero (span31 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
    ·
      by_cases pA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 = 0
      ·
        by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
        ·
          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
          have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((3) : ℂ) (by norm_num) pB0 h
          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB0 h
          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
          have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
          have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
          exact hzero (span30 (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
        ·
          by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
          ·
            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
            have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
            have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB1 h
            have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
            have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
            have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
            exact hzero (span26 (killz nA0 nB0 E0) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
          ·
            by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
            ·
              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
              have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB2 h
              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
              have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
              have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
              exact hzero (span17 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
            ·
              by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
              ·
                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB3 h
                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                exact hzero (span17 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
              ·
                by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
                ·
                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                  have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                  have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                  have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                  have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                  have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                  exact hzero (span22 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                ·
                  by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                  ·
                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                    have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                    have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                    have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                    have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                    have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                    exact hzero (span21 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                  ·
                    by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                    ·
                      have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                      have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                      have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                      have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                      have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                      have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                      have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                      have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                      have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                      have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                      have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                      have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                      exact hzero (span20 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                    ·
                      by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                      ·
                        have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                        have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                        have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                        have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                        have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                        have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                        have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                        have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                        have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                        have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                        have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                        exact hzero (span19 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                      ·
                        by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                        ·
                          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                          have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                          have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                          have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                          have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB8 h
                          exact hzero (span18 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA5 nB9 E9))
                        ·
                          by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                            have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                            have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                            have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                            exact hzero (span17 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) (by norm_num) pA1 h
                            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA1 h
                            have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((0) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA1 h
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                            have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                            have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                            exact hzero (span17 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
      ·
        by_cases pA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 = 0
        ·
          by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
          ·
            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
            have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
            have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((3) : ℂ) (by norm_num) pB0 h
            have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB0 h
            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB0 h
            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
            have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
            have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
            exact hzero (span29 (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
          ·
            by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
            ·
              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
              have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
              have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB1 h
              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB1 h
              have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
              have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
              have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
              exact hzero (span25 (killz nA0 nB0 E0) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
            ·
              by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
              ·
                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB2 h
                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                exact hzero (span16 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
              ·
                by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
                ·
                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                  have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                  have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                  have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                  have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                  have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                  exact hzero (span13 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                ·
                  by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
                  ·
                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                    have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                    have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                    have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                    exact hzero (span7 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
                  ·
                    by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                    ·
                      have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                      have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                      have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                      have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                      have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                      have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                      have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                      have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                      have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                      have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                      have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                      exact hzero (span7 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
                    ·
                      by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                      ·
                        have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                        have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                        have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                        have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                        have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                        have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                        have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                        have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                        have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                        exact hzero (span10 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB7 E7) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                      ·
                        by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                        ·
                          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                          have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                          have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                          have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                          exact hzero (span9 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                        ·
                          by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                            have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                            have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB8 h
                            exact hzero (span8 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA5 nB9 E9))
                          ·
                            by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                            ·
                              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                              have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                              have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                              have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                              exact hzero (span7 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
                            ·
                              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                              have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) (by norm_num) pA2 h
                              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA2 h
                              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                              have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                              have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB7
                              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                              exact hzero (span7 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA4 nB8 E8))
        ·
          by_cases pA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 = 0
          ·
            by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
            ·
              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
              have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((3) : ℂ) (by norm_num) pB0 h
              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB0 h
              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB0 h
              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB0 h
              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
              have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
              exact hzero (span28 (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
            ·
              by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
              ·
                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB1 h
                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB1 h
                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB1 h
                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                exact hzero (span24 (killz nA0 nB0 E0) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
              ·
                by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
                ·
                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                  have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                  have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB2 h
                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB2 h
                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                  have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                  have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                  exact hzero (span15 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                ·
                  by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
                  ·
                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                    have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                    have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB3 h
                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                    have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                    have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                    exact hzero (span12 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                  ·
                    by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
                    ·
                      have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                      have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                      have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                      have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                      have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
                      have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                      have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                      have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                      have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                      have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                      have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                      have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                      exact hzero (span6 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB5 E5) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                    ·
                      by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                      ·
                        have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                        have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                        have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                        have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
                        have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                        have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                        have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                        have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                        have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                        have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                        exact hzero (span4 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA4 nB8 E8) (killz nA5 nB9 E9))
                      ·
                        by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                        ·
                          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                          have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                          exact hzero (span1 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8))
                        ·
                          by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                            have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                            have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                            have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-5) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB7 h
                            exact hzero (span1 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8))
                          ·
                            by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                            ·
                              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                              have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA3 h
                              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                              have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB8 h
                              exact hzero (span2 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA5 nB9 E9))
                            ·
                              by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                              ·
                                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                                exact hzero (span1 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8))
                              ·
                                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pA3 h
                                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB8
                                exact hzero (span1 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8))
          ·
            by_cases pA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 = 0
            ·
              by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
              ·
                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((2) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA4 h
                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB0 h
                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB0 h
                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB0 h
                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                exact hzero (span32 (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA5 nB9 E9))
              ·
                by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
                ·
                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB1 h
                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB1 h
                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB1 h
                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                  have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                  exact hzero (span23 (killz nA0 nB0 E0) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                ·
                  by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
                  ·
                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB2 h
                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB2 h
                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                    have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                    exact hzero (span14 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                  ·
                    by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
                    ·
                      have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                      have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                      have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                      have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                      have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                      have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                      have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                      have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB3 h
                      have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                      have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                      have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                      exact hzero (span11 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                    ·
                      by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
                      ·
                        have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                        have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((2) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA4 h
                        have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                        have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                        have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                        have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                        have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                        have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                        exact hzero (span8 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA3 nB6 E6) (killz nA3 nB7 E7) (killz nA5 nB9 E9))
                      ·
                        by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                        ·
                          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                          have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                          have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                          exact hzero (span3 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                        ·
                          by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                            have nA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := fun h => akill ((1) : ℂ) ((2) : ℂ) ((2) : ℂ) ((-1) : ℂ) (by norm_num) pA4 h
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                            have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                            have nB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-2) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                            exact hzero (span2 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA5 nB9 E9))
                          ·
                            by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                            ·
                              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                              have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                              have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                              exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                            ·
                              by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                              ·
                                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                              ·
                                by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                                ·
                                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                  exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                                ·
                                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                  exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
            ·
              by_cases pA5 : ((2) : ℂ) * a0 + ((-1) : ℂ) * a1 = 0
              ·
                by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                ·
                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                  have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := pA4
                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((3) : ℂ) (by norm_num) pB0 h
                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB0 h
                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB0 h
                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB0 h
                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                  have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                  exact hzero (span27 (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA4 nB8 E8))
                ·
                  by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
                  ·
                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB1 h
                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB1 h
                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB1 h
                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                    have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                    exact hzero (span23 (killz nA0 nB0 E0) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                  ·
                    by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
                    ·
                      have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                      have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                      have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                      have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                      have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                      have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                      have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB2 h
                      have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB2 h
                      have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                      have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                      have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                      exact hzero (span14 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                    ·
                      by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
                      ·
                        have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                        have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                        have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                        have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                        have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB3 h
                        have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                        have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                        have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                        exact hzero (span11 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                      ·
                        by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
                        ·
                          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := pA4
                          have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                          exact hzero (span5 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA4 nB8 E8))
                        ·
                          by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                            exact hzero (span3 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                          ·
                            by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                            ·
                              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := pA4
                              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                              exact hzero (span1 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8))
                            ·
                              by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                              ·
                                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                              ·
                                by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                                ·
                                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                  exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                                ·
                                  by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                                  ·
                                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                    exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                                  ·
                                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                    exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
              ·
                by_cases pB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                ·
                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                  have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := pA4
                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((3) : ℂ) (by norm_num) pB0 h
                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB0 h
                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB0 h
                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB0 h
                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                  have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB0 h
                  exact hzero (span27 (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA4 nB8 E8))
                ·
                  by_cases pB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 = 0
                  ·
                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((4) : ℂ) (by norm_num) pB1 h
                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB1 h
                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB1 h
                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                    have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((3) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB1 h
                    exact hzero (span23 (killz nA0 nB0 E0) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                  ·
                    by_cases pB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 = 0
                    ·
                      have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                      have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                      have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                      have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                      have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                      have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                      have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((5) : ℂ) (by norm_num) pB2 h
                      have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB2 h
                      have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                      have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                      have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((4) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB2 h
                      exact hzero (span14 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                    ·
                      by_cases pB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 = 0
                      ·
                        have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                        have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                        have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                        have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                        have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                        have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                        have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                        have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((1) : ℂ) ((2) : ℂ) (by norm_num) pB3 h
                        have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                        have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                        have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((5) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB3 h
                        exact hzero (span11 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                      ·
                        by_cases pB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 = 0
                        ·
                          have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                          have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                          have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                          have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                          have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := pA4
                          have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                          have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                          have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                          have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                          have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-4) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                          have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                          have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((1) : ℂ) ((2) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB4 h
                          exact hzero (span5 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB5 E5) (killz nA3 nB6 E6) (killz nA4 nB8 E8))
                        ·
                          by_cases pB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                          ·
                            have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                            have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                            have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                            have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                            have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                            have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                            have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                            have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                            have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                            have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-3) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                            have nB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-4) : ℂ) ((1) : ℂ) ((-5) : ℂ) ((1) : ℂ) (by norm_num) pB5 h
                            exact hzero (span3 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA3 nB6 E6) (killz nA3 nB7 E7))
                          ·
                            by_cases pB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                            ·
                              have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                              have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                              have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                              have nA4 : ((1) : ℂ) * a0 + ((2) : ℂ) * a1 ≠ 0 := pA4
                              have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                              have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                              have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                              have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                              have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                              have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                              have nB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := fun h => bkill ((-3) : ℂ) ((1) : ℂ) ((-1) : ℂ) ((1) : ℂ) (by norm_num) pB6 h
                              exact hzero (span1 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA4 nB8 E8))
                            ·
                              by_cases pB7 : ((-5) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                              ·
                                have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                              ·
                                by_cases pB8 : ((-1) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                                ·
                                  have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                  have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                  have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                  have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                  have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                  have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                  have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                  have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                  have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                  have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                  have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                  exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                                ·
                                  by_cases pB9 : ((-2) : ℂ) * b0 + ((1) : ℂ) * b1 = 0
                                  ·
                                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                    exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))
                                  ·
                                    have nA0 : ((1) : ℂ) * a0 + ((0) : ℂ) * a1 ≠ 0 := pA0
                                    have nA1 : ((0) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA1
                                    have nA2 : ((1) : ℂ) * a0 + ((1) : ℂ) * a1 ≠ 0 := pA2
                                    have nA3 : ((1) : ℂ) * a0 + ((-1) : ℂ) * a1 ≠ 0 := pA3
                                    have nB0 : ((1) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB0
                                    have nB1 : ((1) : ℂ) * b0 + ((3) : ℂ) * b1 ≠ 0 := pB1
                                    have nB2 : ((1) : ℂ) * b0 + ((4) : ℂ) * b1 ≠ 0 := pB2
                                    have nB3 : ((1) : ℂ) * b0 + ((5) : ℂ) * b1 ≠ 0 := pB3
                                    have nB4 : ((1) : ℂ) * b0 + ((2) : ℂ) * b1 ≠ 0 := pB4
                                    have nB5 : ((-4) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB5
                                    have nB6 : ((-3) : ℂ) * b0 + ((1) : ℂ) * b1 ≠ 0 := pB6
                                    exact hzero (span0 (killz nA0 nB0 E0) (killz nA0 nB1 E1) (killz nA1 nB2 E2) (killz nA1 nB3 E3) (killz nA2 nB4 E4) (killz nA2 nB5 E5) (killz nA3 nB6 E6))

end Submissions.MinUPB227.ExplicitWitness
