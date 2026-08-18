import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# UndirectedRepetitionThresholdLowerBound — Currie–Mol Theorem 3, for every `k ≥ 6`

> **Theorem 3 (Currie–Mol, arXiv:2006.07474v1).** If `k ≥ 4`, then `URT(k) ≥ (k−1)/(k−2)`,
> and the longest word over `Σ_k` that is undirected `(k−1)/(k−2)`-free has length `k + 3`.

This is the **proved half** of Conjecture 1 — the half the problem's root statement calls "the
lower bound `URT(k) ≥ (k−1)/(k−2)` for all `k ≥ 4` is the paper's Theorem 3 and is proved" —
and nothing in this graph had it. Here it is, for every `k ≥ 6`.

All five definitions are copied character for character from
`Statements.UndirectedRepetitionThreshold`, including `factor w i n = (List.range n).map fun j
=> w (i + j)` with `w (i + j)` and not `w (j + i)`, so this is a statement about the root's own
`URT` and not a lookalike.

## The argument

Everything reduces to one certificate: in an undirected `r`-free word, a block of length `l`
may not reoccur — forwards **or reversed** — after a gap `m` whenever `r(l+m) ≤ 2l+m`. At
`r = (k−1)/(k−2)` that is `m + 3l ≤ lk`. Two instances are used:

* `l = 1`: two equal letters are at distance `≥ k−1`, so any `k−1` consecutive letters are
  distinct and, `Σ_k` having `k` letters, exactly one letter is missing from each window;
* `l = 2`: an adjacent pair may not reoccur, in either order, after a gap `m ≤ 2k−6`.

The first makes each next letter one of exactly **two** choices — the letter leaving the window
or the missing one — which is what a `Nodup` list of `k` letters over `Fin k` being all of
`Fin k` gives. Following those choices from a window `w 0 … w (k−2)` produces the tree of
Currie–Mol's Figure 1, with **eleven** leaves, each killed by the `l = 2` instance. Both side
conditions are tight: at `m = 2k−5` and at `d = k−1` the exponent inequality is false, so
neither is an accidentally-always-true bound.

`k ≥ 6` is exactly the hypothesis the uniform tree needs: the deepest branch reads the letters
at positions `0,1,2,3,4` of the opening window, which requires `4 ≤ k−2`. Currie–Mol handle
`k ∈ {4,5}` by a separate backtracking check, and this statement does **not** cover them.

## Scope

Covers `URT(k) ≥ (k−1)/(k−2)` for every `k ≥ 6`, and hence also (since the value is `> 1`)
that no infinite word over `Σ_k` is undirected `(k−1)/(k−2)`-free. Does NOT cover `k = 4, 5`;
does NOT cover the upper bound, which is the open half of Conjecture 1; and says nothing about
the length-`k+3` sharpness clause of the paper's Theorem 3.
-/

namespace Statements.UndirectedRepetitionThresholdLowerBound
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


/-- The canonical proposition: Currie–Mol's Theorem 3, the proved half of their Conjecture 1,
for every `k ≥ 6`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 6 ≤ k → ((k : ℝ) - 1) / ((k : ℝ) - 2) ≤ URT k

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UndirectedRepetitionThresholdLowerBound
