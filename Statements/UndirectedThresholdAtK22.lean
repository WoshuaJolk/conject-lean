import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# UndirectedThresholdAtK22 — Currie–Mol Conjecture 1 at the first open value

`URT(22) = 21/20`. Currie–Mol (arXiv:2006.07474v1) prove `URT(k) ≥ (k−1)/(k−2)` for every
`k ≥ 4` (Theorem 3) and confirm equality for `k ∈ {4,…,21}` (Theorem 5). `k = 22` is the
smallest value for which nothing is known, and it has been open since 2020.

The five definitions below are VERBATIM from `Statements/UndirectedRepetitionThreshold.lean`,
so a proof of this statement is literally the root statement instantiated at `k = 22`. This is
a scoped sub-instance, not a decomposition: proving it does not prove the root.

## Why `k = 22` specifically, and what is already in hand

The route that settled `k ≤ 21` reduces the whole problem, at a fixed `k`, to finding ONE
uniform binary morphism `f_k` with the Moulin-Ollagnier algebraic property
`∃ φ ∈ S_k, φ · τ(f(a)) · φ⁻¹ = τ(a)` for `a ∈ {1,2}`, where `τ = σ ∘ g` and `g` is already
fixed at `g(1) = 31`, `g(2) = 12` for every `k ∉ {5,6,8}`. Extrapolating the published
`|f_4| = 11 … |f_21| = 23`, `f_22` is plausibly a uniform binary morphism of length ≲ 30.
Everything after that is a finite check.

EVIDENCE, and it is evidence and not proof: a backtracking search over the ternary Pansiot
encoding at `k = 22`, run in this session, produced an undirected `(21/20)⁺`-free word over
`Σ₂₂` of more than 120,000 letters with no backtracking pressure, and a 1500-letter prefix of
it was re-verified by a second instrument over the UNRESTRICTED period range. Controls in both
directions on the same instruments: the known-free cases `k = 20, 21` run long, and every
threshold placed below Dejean's bound (`k=9/M=9`, `k=9/M=10`, `k=12/M=12`, `k=22/M=22`)
exhausts at length ≤ 23. A finite free word is not an infinite one: promoting it needs the
morphism and the descent. So this is a labelled target with evidence attached, not a claim.
-/

namespace Statements.UndirectedThresholdAtK22


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

/-- The canonical proposition: Conjecture 1 at `k = 22`, the first open value.
`(22 - 1)/(22 - 2) = 21/20`, formed by real subtraction and real division of the cast. -/
abbrev statement : Prop := URT 22 = ((22 : ℝ) - 1) / ((22 : ℝ) - 2)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UndirectedThresholdAtK22
