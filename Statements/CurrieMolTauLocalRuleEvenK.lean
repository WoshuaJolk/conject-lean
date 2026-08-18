import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

/-!
# CurrieMolTauLocalRuleEvenK — `τ(f_k(1))` has a description with no `k` in it

Every result on Currie–Mol's Conjecture 1 above `k = 21` so far has been obtained one `k` at a
time, because the object the Moulin-Ollagnier descent needs to understand,

    τ(f_k(1)) = ρ^α · (k-1,k) · ρ^β · (k-1,k),

is a product whose length grows with `k`. This statement removes that growth for one explicit
family. In the cycle coordinates of `Statements.RhoCycleStructureEvenK` — `eC` on
`C₁ = {1} ∪ evens` (length `k/2+1`) and `oC` on `C₂ = {3,…,k-1}` (length `k/2-1`) —
`τ(f_k(1))` is given, for EVERY even `k ≥ 20` at once, by a rule whose only `k`-dependence is
the two block lengths:

* on `C₁`: coordinate `↦` coordinate `+ 2`, cyclically;
* on `C₂`: coordinate `↦` coordinate `+ 4`, cyclically;
* except at four letters, where it crosses between the blocks:
  `C₁` coordinate `k/2` (the letter `k`) `↦` `C₂` coordinate `3`;
  `C₁` coordinate `5` `↦` `C₂` coordinate `7`;
  `C₂` coordinate `k/2-2` (the letter `k-1`) `↦` `C₁` coordinate `1`;
  `C₂` coordinate `3` `↦` `C₁` coordinate `7`.

The four exceptional coordinates and the four landing coordinates are absolute constants. The
two exceptional sources are exactly `k` and `k-1` — the pair that `τ(1)⁻¹τ(2)` transposes —
and one fixed coordinate in each block.

The morphism is `f_k(1) = 1⁷ 2 1^{(k-12)/2} 2`, the family that the constructions at
`https://jig.so/p/3?s=13` follow at `k ≡ 0 (mod 4)`. `τ` is spelled with Currie–Mol's
`g(1) = 31`, `g(2) = 12` through `τ(1) = ρ` and `τ(2) = ρ ∘ (k-1,k)`, the last letter of a word
acting first, and `ρ` is spelled character for character as in `Statements.TauNormalForm`. The
cyclic advance is written mod-free as two guarded cases, as in `Statements.RhoCycleStructure`,
because the modulus is a variable.

## What this is for, and what it is not

The Moulin-Ollagnier algebraic property at even `k` amounts to: `τ(f_k(1))` has the same cycle
type as `ρ`, namely `(k/2+1, k/2-1)`, with `k` and `k-1` in different cycles. Establishing that
symbolically in `k` — as opposed to recomputing it for each `k` — needs a description of
`τ(f_k(1))` that does not grow with `k`, and this is that description. The cycle-type
conclusion itself is NOT proved here; it needs an orbit argument on top of this rule, and that
argument is not formalised.

Two things this does not do, stated because they bound the route. First, it settles no case of
the conjecture: the algebraic property is one hypothesis of Currie–Mol's Theorem 5, and the
freeness of the decoded word is a separate matter — for this family the decoded word was
checked in the session that produced this statement and is NOT undirected `((k-1)/(k-2))⁺`-free
at `k = 64`, the first failure being at position 19 854, so the family does not give an
infinite sequence of constructions and no `k`-uniform algebraic property could make it. Second,
an exhaustive scan over `α, β ≤ 30` against every even `k` in `[20, 80]` found no pair of
CONSTANTS that works for all `k`, so a family whose morphism length does not grow with `k` does
not exist in this shape. What is uniform here is the description, not the morphism.
-/

namespace Statements.CurrieMolTauLocalRuleEvenK

def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2
def tt (k j : ℕ) : ℕ := if j = k - 1 then k else if j = k then k - 1 else j
def tauL (k c j : ℕ) : ℕ := if c = 1 then rho k j else rho k (tt k j)
def tauW (k : ℕ) (u : List ℕ) (j : ℕ) : ℕ := u.foldr (tauL k) j
def fOne (k : ℕ) : List ℕ := List.replicate 7 1 ++ (2 :: (List.replicate ((k - 12) / 2) 1 ++ [2]))
def inC1 (k j : ℕ) : Prop := j = 1 ∨ (2 ≤ j ∧ j ≤ k ∧ j % 2 = 0)
def inC2 (k j : ℕ) : Prop := 3 ≤ j ∧ j + 1 ≤ k ∧ j % 2 = 1
def eC (j : ℕ) : ℕ := if j = 1 then 0 else j / 2
def oC (j : ℕ) : ℕ := (j - 3) / 2


/-- For every even `k ≥ 20`, `τ(f_k(1))` obeys a rule with NO `k` in it beyond the two block
lengths: on `C₁` it advances the coordinate by `2`, on `C₂` by `4`, except at four letters —
the two ends of the blocks (coordinates `k/2` in `C₁` and `k/2-2` in `C₂`, which are exactly
the letters `k` and `k-1` that `τ(1)⁻¹τ(2)` transposes) and the two fixed coordinates `5` in
`C₁` and `3` in `C₂` — where it crosses to the other block and lands at the fixed coordinates
`3`, `1`, `7`, `7`. Cyclic advance is written mod-free as two guarded cases. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 20 ≤ k → k % 2 = 0 → ∀ j : ℕ,
    (inC1 k j → eC j = k / 2 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = 3) ∧
    (inC1 k j → eC j = 5 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = 7) ∧
    (inC1 k j → eC j ≠ k / 2 → eC j ≠ 5 → eC j + 2 ≤ k / 2 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = eC j + 2) ∧
    (inC1 k j → eC j ≠ k / 2 → eC j ≠ 5 → k / 2 < eC j + 2 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = eC j + 2 - (k / 2 + 1)) ∧
    (inC2 k j → oC j + 2 = k / 2 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = 1) ∧
    (inC2 k j → oC j = 3 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = 7) ∧
    (inC2 k j → oC j + 2 ≠ k / 2 → oC j ≠ 3 → oC j + 6 ≤ k / 2 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = oC j + 4) ∧
    (inC2 k j → oC j + 2 ≠ k / 2 → oC j ≠ 3 → k / 2 < oC j + 6 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = oC j + 4 - (k / 2 - 1))

/-- The open target. -/
theorem target : statement := sorry

end Statements.CurrieMolTauLocalRuleEvenK
