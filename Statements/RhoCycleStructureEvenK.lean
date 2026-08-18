import Mathlib.Data.List.Basic

/-!
# RhoCycleStructureEvenK — the cycle coordinates of `τ(1)` at even `k`

`Statements.RhoCycleStructure` puts `ρ = τ(1)` into cycle coordinates for ODD `k`, where it is
a single `k`-cycle, and says so in its scope: it covers "odd `k ≥ 5` only", and "does NOT cover
even `k`, where `ρ` is not a `k`-cycle at all (it has cycle type `(k/2+1, k/2-1)`)". This is
that missing half, in the same mod-free style.

For even `k ≥ 6` the letters split into two `ρ`-invariant blocks:

* `C₁ = {1} ∪ {even letters}`, of size `k/2 + 1`, on which `ρ` cycles
  `1 → 2 → 4 → 6 → ⋯ → k-2 → k → 1`;
* `C₂ = {3, 5, …, k-1}`, of size `k/2 - 1`, on which `ρ` cycles `3 → 5 → ⋯ → k-1 → 3`.

`eC` and `oC` are the relabellings into `{0,…,k/2}` and `{0,…,k/2-2}`; the statement says they
are bijections onto those segments and that they carry `ρ` to "add one cyclically". As in
`RhoCycleStructure` the cyclic step is stated as two mod-free cases, since the modulus is a
variable. Together the clauses say exactly: **for even `k`, `ρ` has cycle type
`(k/2+1, k/2-1)`.**

The last two clauses locate the pair that matters downstream: `τ(1)⁻¹τ(2)` is the
transposition `(k-1, k)`, and `k` sits at the LAST coordinate of `C₁` while `k-1` sits at the
LAST coordinate of `C₂` — one point in each block, at a known place. That is the input any
argument about `τ(f(1)) = ρ^α · (k-1,k) · ρ^β · (k-1,k)` needs in order to have a description
that does not depend on `k`.

The first clause, `σ(3)(σ(1)(j)) = ρ(j)`, is the bridge that makes all of this a statement
about Currie–Mol's `τ(1)` rather than about a free-standing permutation; `sig` and `rho` are
spelled character for character as in `Statements.TauNormalForm`, which carries that identity
with a green proof.

## Scope, honestly

This is a statement about one permutation. It does not touch `URT(k)`, rules out no
construction, and proves no case of the conjecture. Its purpose is infrastructure: it is the
coordinate system in which a Currie–Mol morphism's `τ(f(1))` acquires a `k`-independent
description, which is the first step of any attempt to establish the Moulin-Ollagnier
algebraic property symbolically in `k` rather than one `k` at a time.
-/

namespace Statements.RhoCycleStructureEvenK

/-- Currie–Mol's `σ(m)` on the letter `j` of `Σ_k = {1,…,k}`, two-row notation. Identical,
character for character, to `Statements.TauNormalForm.sig`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `ρ`, the step-2 map `τ(1) = σ(3) ∘ σ(1)`: `1 ↦ 2`, `j ↦ j+2` for `2 ≤ j ≤ k-2`,
`k-1 ↦ 3`, `k ↦ 1`. Identical to `Statements.TauNormalForm.rho`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

/-- The first block: the letter `1` together with the even letters. -/
def inC1 (k j : ℕ) : Prop := j = 1 ∨ (2 ≤ j ∧ j ≤ k ∧ j % 2 = 0)

/-- The second block: the odd letters from `3` to `k-1`. -/
def inC2 (k j : ℕ) : Prop := 3 ≤ j ∧ j + 1 ≤ k ∧ j % 2 = 1

/-- Cycle coordinate on the first block: `1 ↦ 0` and `2m ↦ m`. -/
def eC (j : ℕ) : ℕ := if j = 1 then 0 else j / 2

/-- Cycle coordinate on the second block: `2m+1 ↦ m-1`, i.e. `3 ↦ 0`. -/
def oC (j : ℕ) : ℕ := (j - 3) / 2

/-- For every even `k ≥ 6`: `τ(1) = ρ`; the letters split into the two `ρ`-invariant blocks
`C₁` (the letter `1` and the evens, size `k/2+1`) and `C₂` (the odds from `3` to `k-1`, size
`k/2-1`); `eC` and `oC` are bijections from those blocks onto `{0,…,k/2}` and `{0,…,k/2-2}`
carrying `ρ` to "add one cyclically"; and the two letters `k-1`, `k` that `τ(1)⁻¹τ(2)`
transposes sit at the LAST coordinate of their respective blocks. Equivalently: for even `k`,
`ρ` has cycle type `(k/2+1, k/2-1)`. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 6 ≤ k → k % 2 = 0 →
    (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 3 (sig k 1 j) = rho k j) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (inC1 k j ∨ inC2 k j)) ∧
    (∀ j : ℕ, ¬ (inC1 k j ∧ inC2 k j)) ∧
    (∀ j : ℕ, inC1 k j → inC1 k (rho k j)) ∧
    (∀ j : ℕ, inC2 k j → inC2 k (rho k j)) ∧
    (∀ j : ℕ, inC1 k j → eC j ≤ k / 2) ∧
    (∀ i : ℕ, i ≤ k / 2 → ∃ j : ℕ, inC1 k j ∧ eC j = i) ∧
    (∀ j j' : ℕ, inC1 k j → inC1 k j' → eC j = eC j' → j = j') ∧
    (∀ j : ℕ, inC2 k j → oC j + 2 ≤ k / 2) ∧
    (∀ i : ℕ, i + 2 ≤ k / 2 → ∃ j : ℕ, inC2 k j ∧ oC j = i) ∧
    (∀ j j' : ℕ, inC2 k j → inC2 k j' → oC j = oC j' → j = j') ∧
    (∀ j : ℕ, inC1 k j → eC j < k / 2 → eC (rho k j) = eC j + 1) ∧
    (∀ j : ℕ, inC1 k j → eC j = k / 2 → eC (rho k j) = 0) ∧
    (∀ j : ℕ, inC2 k j → oC j + 2 < k / 2 → oC (rho k j) = oC j + 1) ∧
    (∀ j : ℕ, inC2 k j → oC j + 2 = k / 2 → oC (rho k j) = 0) ∧
    (inC1 k k ∧ eC k = k / 2) ∧
    (inC2 k (k - 1) ∧ oC (k - 1) + 2 = k / 2)

/-- The open target. -/
theorem target : statement := sorry

end Statements.RhoCycleStructureEvenK
