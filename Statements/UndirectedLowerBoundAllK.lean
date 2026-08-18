import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# UndirectedLowerBoundAllK — Currie–Mol Theorem 3, complete

> **Theorem 3 (Currie–Mol, arXiv:2006.07474v1).** If `k ≥ 4`, then `URT(k) ≥ (k−1)/(k−2)`.

This is the **whole** proved half of Conjecture 1, for **every** `k ≥ 4`.
`Statements.UndirectedRepetitionThresholdLowerBound` is the same bound for `k ≥ 6` only — the
range the uniform tree covers — and this statement adds the two values Currie–Mol handle by a
separate backtracking check, `k = 4` and `k = 5`. Nothing there is retracted: it is correct and
this is strictly stronger.

All five definitions are copied character for character from
`Statements.UndirectedRepetitionThreshold`, including `factor w i n = (List.range n).map fun j
=> w (i + j)` with `w (i + j)` and not `w (j + i)`.

## The argument

One certificate does all the work: in an undirected `r`-free word a block of length `l` may not
reoccur, forwards **or reversed**, after a gap `m` whenever `r(l+m) ≤ 2l+m`; at
`r = (k−1)/(k−2)` that reads `m + 3l ≤ lk`. Its `l = 1` instance says two equal letters are at
distance `≥ k−1`, so every `k−1` consecutive letters are distinct and — since a `Nodup` list of
`k` letters over `Fin k` is all of `Fin k` — each next letter is one of exactly **two**: the one
leaving the window, or the one missing from it. Following those choices gives a finite tree, and
every leaf is killed by the `l = 2` instance with a gap of `k−3`, `k−2` or `k−1`.

Three trees are needed, because the uniform one reads positions `0,1,2,3,4` of the opening
window and so needs `4 ≤ k−2`:

* `k ≥ 6`: the uniform tree, eleven leaves, written with `k = q + 6` so no natural subtraction
  occurs — this is Currie–Mol's Figure 1;
* `k = 5`: twelve leaves; one of them cannot use the uniform certificate because position `4`
  has collided with position `k−1`, and uses the pair `(w 3, w 4)` instead;
* `k = 4`: twelve leaves, one level deeper, and two leaves close on the missing letter itself.

Both side conditions are tight — at `m = 2k−5` and at `d = k−1` the exponent inequality is
false — so no leaf closes for a void reason.

## Scope

Covers `URT(k) ≥ (k−1)/(k−2)` for every integer `k ≥ 4`, hence also that no infinite word over
`Σ_k` is undirected `(k−1)/(k−2)`-free. Does NOT cover the upper bound, which is the open half
of Conjecture 1. Does NOT cover the sharpness clause of the paper's Theorem 3 — that the longest
undirected `(k−1)/(k−2)`-free word over `Σ_k` has length exactly `k+3` — only the
non-existence of an infinite one. Says nothing about `k = 3`.
-/

namespace Statements.UndirectedLowerBoundAllK
variable {α : Type*}

def IsUndirectedPower (r : ℝ) (z : List α) : Prop :=
  ∃ x y x' : List α,
    z = x ++ y ++ x' ∧ x ≠ [] ∧ (x' = x ∨ x' = x.reverse) ∧
      (z.length : ℝ) = r * ((x ++ y).length : ℝ)

def factor (w : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => w (i + j)

def UndirectedFree (r : ℝ) (w : ℕ → α) : Prop :=
  ∀ (i n : ℕ) (s : ℝ), r ≤ s → ¬ IsUndirectedPower s (factor w i n)

def Avoidable (k : ℕ) (r : ℝ) : Prop := ∃ w : ℕ → Fin k, UndirectedFree r w

noncomputable def URT (k : ℕ) : ℝ := sInf {r : ℝ | Avoidable k r}


/-- The canonical proposition: Currie–Mol's Theorem 3, in full — the proved half of their
Conjecture 1, for every `k ≥ 4`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k → ((k : ℝ) - 1) / ((k : ℝ) - 2) ≤ URT k

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UndirectedLowerBoundAllK
