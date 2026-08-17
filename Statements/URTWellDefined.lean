import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# URTWellDefined — the root's `sInf` is a genuine infimum, and its power predicate is inhabited

`Statements/UndirectedRepetitionThreshold.lean` defines `URT k` as `sInf {r | Avoidable k r}`.
An `sInf` over an empty or unbounded-below set is a junk value in Mathlib, and a power predicate
that no word satisfies would make every `r` avoidable — either way Currie–Mol's Conjecture 1
would be a statement about nothing. That the root escapes both is asserted in its pose message.
**This statement is that assertion, labelled, so it can be machine-checked instead of believed.**

The five definitions below are VERBATIM from the root, so this is a claim about the root's own
vocabulary and not about a lookalike.

Three conjuncts:

1. `IsUndirectedPower` is satisfiable — a concrete square `[0,0]` over `Fin 4` at `r = 2`.
2. It is satisfiable *on the reversal branch* too — `[0,1,1,0] = x y xᴿ` with `x = [0,1]`. Without
   this the definition could be right about ordinary powers and vacuous about reverse ones, which
   is precisely the half that distinguishes `URT` from Dejean's `RT`.
3. For every nonempty alphabet, `1 ≤ URT k ≤ 2`. Upper: every `r > 2` is vacuously avoidable
   (an undirected power has exponent `(2|x|+|y|)/(|x|+|y|) ≤ 2`), so the set is nonempty and
   `sInf ≤ 2`. Lower: pigeonhole — an infinite word over a finite alphabet repeats a letter
   `w i = w j`, and `w i … w j` is an undirected `((p+2)/(p+1))`-power with exponent `> 1`, so no
   `r ≤ 1` is avoidable and the set is bounded below by 1.

Consequence, and the reason this is worth a label: `URT k` lies in `[1,2]`, so it is a real
infimum of a nonempty set that is bounded below, and the conjectured value `(k-1)/(k-2) ≤ 3/2`
sits strictly inside that range for every `k ≥ 4`. Conjecture 1 is therefore a statement that
could be false, which is the minimum bar for it being worth proving.
-/

namespace Statements.URTWellDefined


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

/-- The canonical proposition. -/
abbrev statement : Prop :=
  IsUndirectedPower (2 : ℝ) ([0, 0] : List (Fin 4)) ∧
  IsUndirectedPower (2 : ℝ) ([0, 1, 1, 0] : List (Fin 4)) ∧
  (∀ k : ℕ, 0 < k → 1 ≤ URT k ∧ URT k ≤ 2)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.URTWellDefined
