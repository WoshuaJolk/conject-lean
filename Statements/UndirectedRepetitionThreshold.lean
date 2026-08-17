import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# UndirectedRepetitionThreshold — Currie–Mol, Conjecture 1

Source, read as PDF (`pdftotext`) in this session: J. D. Currie and L. Mol, *The undirected
repetition threshold*, arXiv:2006.07474v1 [math.CO] 12 Jun 2020 = Theoretical Computer Science
866 (2021) 51–63.

> **Conjecture 1.** For every `k ≥ 4`, we have `URT(k) = (k − 1)/(k − 2)`.

The definitions below are transcribed term by term from the paper's Section 1.

* "an `r`-power up to `∼` [is] a word of the form `xyx′`, where `x` is a nonempty word, and we
  have both `x′ ∼ x` and `|xyx′|/|xy| = r`" — with `∼` = `≃`, i.e. `x′ ∈ {x, xᴿ}`.
  → `IsUndirectedPower`.
* "a word `w` is called `α`-free up to `∼` if no factor of `w` is an `r`-power up to `∼` for
  `r ≥ α`" → `UndirectedFree` (note: `r ≥ α`, not `r = α`).
* "`α`-powers up to `∼` are `k`-avoidable if there is an infinite word on `k` letters that is
  `α`-free up to `∼`" → `Avoidable`.
* "`RT∼(k) = inf{r : r-powers up to ∼ are k-avoidable}`" → `URT`.

## Where this differs from the paper, and why it does not matter for `k ≥ 4`

The paper defines `r`-powers only for `1 < r ≤ 2`, and consequently allows `RT∼(k) = ∞` when the
defining set is empty. Here `IsUndirectedPower r z` is stated for every real `r` and is simply
*false* outside `(1, 2]`: with `|x| ≥ 1`, `|xyx′|/|xy| = (2|x|+|y|)/(|x|+|y|) ∈ (1, 2]` always.
Hence

* no `r ≤ 1` is avoidable (any infinite word over a finite alphabet repeats a letter, which
  gives an undirected `s`-power with `s ∈ (1,2]`, so `s ≥ r`), so the set is bounded below by 1;
* every `r > 2` is vacuously avoidable, so the set is nonempty and `sInf ≤ 2`.

So `{r | Avoidable k r}` is exactly the paper's set together with `(2, ∞)`, and the two infima
agree whenever the paper's value is finite. For every `k ≥ 4` it is: `URT(k) ≤ ART(k)` and
Abelian squares are 4-avoidable (Keränen), so the paper's `URT(k) ≤ 2`. On the range the
statement quantifies over, `URT` below is the paper's `URT`.

`(k - 1)/(k - 2)` is real subtraction and real division of the *cast* `(k : ℝ)`; it is **not**
natural subtraction or natural division. For `k ≥ 4` the denominator is at least 2.

## What a solution looks like

The lower bound `URT(k) ≥ (k−1)/(k−2)` for all `k ≥ 4` is the paper's Theorem 3 and is proved.
The open half is the upper bound, and its certificate is an exhibited infinite word over `Σ_k`
that is undirected `((k−1)/(k−2))⁺`-free. The paper supplies one for each `k ∈ {4,…,21}`
(its Theorem 5); nothing is known for any `k ≥ 22`.
-/

namespace Statements.UndirectedRepetitionThreshold

variable {α : Type*}

/-- An **undirected `r`-power**: a word `xyx′` with `x` nonempty, `x′ ∈ {x, xᴿ}`, and
`|xyx′|/|xy| = r`. Currie–Mol Section 1, verbatim. The ratio is written as the multiplication
`|xyx′| = r * |xy|` to avoid a division; `|xy| ≥ 1` because `x` is nonempty. -/
def IsUndirectedPower (r : ℝ) (z : List α) : Prop :=
  ∃ x y x' : List α,
    z = x ++ y ++ x' ∧ x ≠ [] ∧ (x' = x ∨ x' = x.reverse) ∧
      (z.length : ℝ) = r * ((x ++ y).length : ℝ)

/-- The length-`n` factor of the infinite word `w` beginning at position `i`. -/
def factor (w : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => w (i + j)

/-- `w` is **undirected `r`-free**: no factor of `w` is an undirected `s`-power for any
`s ≥ r`. Currie–Mol Section 1: "`α`-free up to `∼` if no factor of `w` is an `r`-power up to
`∼` for `r ≥ α`". -/
def UndirectedFree (r : ℝ) (w : ℕ → α) : Prop :=
  ∀ (i n : ℕ) (s : ℝ), r ≤ s → ¬ IsUndirectedPower s (factor w i n)

/-- Undirected `r`-powers are **`k`-avoidable**: some infinite word on `k` letters is
undirected `r`-free. -/
def Avoidable (k : ℕ) (r : ℝ) : Prop := ∃ w : ℕ → Fin k, UndirectedFree r w

/-- The **undirected repetition threshold** `URT(k) = inf {r : undirected r-powers are
k-avoidable}`. -/
noncomputable def URT (k : ℕ) : ℝ := sInf {r : ℝ | Avoidable k r}

/-- The canonical proposition: Currie–Mol's Conjecture 1. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k → URT k = ((k : ℝ) - 1) / ((k : ℝ) - 2)

/-- The open target. A submission proves `statement` in its own module; the verifier bridges
the two. Replacing this `sorry` is not how the problem is solved. -/
theorem target : statement := sorry

end Statements.UndirectedRepetitionThreshold
