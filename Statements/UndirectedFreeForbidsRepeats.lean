import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# UndirectedFreeForbidsRepeats — what undirected freeness actually forbids

Everything on this problem — Currie–Mol's lower bound (their Theorem 3), the ternary Pansiot
encoding their constructions run through (their §4.1), and every backtracking search anyone
runs here — rests on one arithmetic fact, and until now that fact lived only in prose:

> in an undirected `r`-free word, a block of length `l` may not reoccur, forwards **or
> reversed**, after a gap `m`, whenever `r·(l+m) ≤ 2l+m`.

This statement is that fact, in the root statement's own vocabulary, plus the two
specialisations everything downstream actually uses.

## The two specialisations, and why they are stated for `α⁺`-freeness

Currie–Mol's Theorem 3 says the longest undirected `((k−1)/(k−2))`-free word over `Σ_k` has
length `k + 3`. So for `k ≥ 4` **no infinite word is undirected `((k−1)/(k−2))`-free**, and a
lemma hypothesising that of a `w : ℕ → Fin k` would be vacuously true — a perfectly checked
theorem about nothing. The satisfiable hypothesis, and the one Currie–Mol's constructions
satisfy, is `α⁺`-freeness: `w` is undirected `r`-free for **every** `r > (k−1)/(k−2)`. That is
how clause 2 is stated. Under it:

* two equal letters must be at distance `≥ k − 2`: `1 ≤ d ≤ k − 3` forces `w i ≠ w (i+d)`,
  since `(d+1)/d > (k−1)/(k−2)` exactly when `d < k − 2`. Hence every factor of length `k − 2`
  has `k − 2` distinct letters — the hypothesis the ternary encoding needs;
* a **pair** of adjacent letters may not reoccur, in either order, after a gap `m ≤ 2k − 7`,
  since `(m+4)/(m+2) > (k−1)/(k−2)` exactly when `m < 2k − 6`. Every one of the eleven leaves
  of the tree in Currie–Mol's Figure 1 is an instance of this single clause.

Natural subtraction is avoided throughout: `d + 3 ≤ k` and `m + 7 ≤ 2k` and `1 ≤ l`.

## Non-vacuity

Clause 1 is non-vacuous: at `r = 2` its hypothesis says `w` has no square and no even
palindrome as a factor, which Currie–Mol's own `URT(3) = 7/4` word satisfies, and its
arithmetic side condition `2(l+m) ≤ 2l+m` then holds exactly at `m = 0`. Clause 2's hypothesis
is satisfied by every word Currie–Mol construct in their Theorem 5. In the other direction, the
*conclusion* of clause 2 is false for the constant word over `Fin 4`, so the hypothesis is
load-bearing rather than decorative.

`IsUndirectedPower`, `factor` and `UndirectedFree` are copied character for character from
`Statements.UndirectedRepetitionThreshold`, including `factor w i n = (List.range n).map fun j
=> w (i + j)` with `w (i + j)` and not `w (j + i)`.
-/

namespace Statements.UndirectedFreeForbidsRepeats
variable {α : Type*}

def IsUndirectedPower (r : ℝ) (z : List α) : Prop :=
  ∃ x y x' : List α,
    z = x ++ y ++ x' ∧ x ≠ [] ∧ (x' = x ∨ x' = x.reverse) ∧
      (z.length : ℝ) = r * ((x ++ y).length : ℝ)

def factor (w : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => w (i + j)

def UndirectedFree (r : ℝ) (w : ℕ → α) : Prop :=
  ∀ (i n : ℕ) (s : ℝ), r ≤ s → ¬ IsUndirectedPower s (factor w i n)

abbrev statement : Prop :=
  ∀ (k : ℕ) (w : ℕ → Fin k),
    (∀ (r : ℝ), UndirectedFree r w →
        ∀ i l m : ℕ, 1 ≤ l → r * ((l : ℝ) + (m : ℝ)) ≤ 2 * (l : ℝ) + (m : ℝ) →
          factor w (i + l + m) l ≠ factor w i l ∧
          factor w (i + l + m) l ≠ (factor w i l).reverse)
    ∧ (4 ≤ k → (∀ r : ℝ, ((k : ℝ) - 1) / ((k : ℝ) - 2) < r → UndirectedFree r w) →
        (∀ i d : ℕ, 1 ≤ d → d + 3 ≤ k → w i ≠ w (i + d)) ∧
        (∀ i m : ℕ, m + 7 ≤ 2 * k →
          ¬ (w (i + 2 + m) = w i ∧ w (i + 3 + m) = w (i + 1)) ∧
          ¬ (w (i + 2 + m) = w (i + 1) ∧ w (i + 3 + m) = w i)))


/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UndirectedFreeForbidsRepeats
