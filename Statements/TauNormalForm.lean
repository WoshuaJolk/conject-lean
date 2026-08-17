import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# TauNormalForm — the bridge from Currie–Mol's `σ` to the step-2 permutation `ρ`

`Statements/PansiotCycleDistanceRigidity.lean` proves an abstract fact: cyclic distance is a
complete invariant, up to sign, of a pair (`k`-cycle, `k`-cycle composed with a transposition of
two of its points) under simultaneous conjugacy. That statement is proved, but its **relevance**
to Currie–Mol rests on a computation, and until now that computation lived only in Python. This
file is that computation, stated so a kernel can check it.

## The source, verbatim

Currie–Mol (arXiv:2006.07474v1, §4.1) define a morphism `σ : Σ₃* → S_k` by, in their two-row
notation on the letters `Σ_k = {1,…,k}`:

```
σ(1) = (1 2 3 4 … k-1 k) ↦ (2 3 4 5 …  k  1)
σ(2) = (1 2 3 4 … k-1 k) ↦ (1 3 4 5 …  k  2)
σ(3) = (1 2 3 4 … k-1 k) ↦ (1 2 4 5 …  k  3)
```

The uniform pattern, which is what `sig` below encodes: `σ(m)` fixes `1,…,m-1`, sends `j ↦ j+1`
for `m ≤ j ≤ k-1`, and sends `k ↦ m`. Their constructions factor through `g : Σ₂* → Σ₃*` with
`g(1) = 31`, `g(2) = 12` (their fixed choice for every `k ∉ {5,6,8}`), giving `τ = σ ∘ g`.

**Composition convention.** `σ` is a morphism, so `σ(ab) = σ(a)σ(b)`, and the product is ordinary
function composition — rightmost applied first. This is not a free choice: it is pinned by their
own worked control `σ(3123131231) = id` over `Σ₄`, which the opposite convention fails. So
`τ(1) = σ(g(1)) = σ(31) = σ(3) ∘ σ(1)`, i.e. apply `σ(1)` first.

## What is claimed

For every `k ≥ 4`, on the letters `1 ≤ j ≤ k`:

* `sig` really is a permutation of `{1,…,k}` for every `1 ≤ m ≤ k` — it maps the range into
  itself and is injective on it. (Stated so that "these are elements of `S_k`" is part of the
  claim rather than an aside.)
* **`τ(1) = ρ`**, where `ρ : 1 ↦ 2, j ↦ j+2 for 2 ≤ j ≤ k-2, k-1 ↦ 3, k ↦ 1` — the *step-2* map.
* **`τ(2) = ρ ∘ (k-1, k)`**, the transposition applied first.
* **`σ(2) = σ(1) ∘ (1, k)`** — Pansiot's binary pair is the same shape with the transposition at
  cyclic distance **1**, which is the comparison the rigidity statement then rules out.

Verified in exact integer permutation arithmetic for every `k` in `4…61` before being stated; a
proof of this discharges that range and every `k` beyond it.

## Why it is worth a label

Without this, one of the two dead routes on this problem has a machine-checked core and a
hand-checked connection to the paper it is about — and the connection is the part more likely to
be wrong, because it is a transcription of someone's `σ` rather than a textbook fact. Filing the
elimination without filing the bridge is the mistake this problem's own contributor brief records
as failure 7.
-/

namespace Statements.TauNormalForm

/-- `σ(m)` on the letter `j`: fixes `1,…,m-1`, shifts `m ≤ j ≤ k-1` up by one, sends `k ↦ m`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `ρ`, the step-2 map: `1 ↦ 2`, `j ↦ j+2` for `2 ≤ j ≤ k-2`, `k-1 ↦ 3`, `k ↦ 1`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

/-- The transposition `(k-1, k)`, i.e. `τ(1)⁻¹τ(2)`. -/
def swapLast (k j : ℕ) : ℕ := if j = k - 1 then k else if j = k then k - 1 else j

/-- The transposition `(1, k)`, i.e. `σ(1)⁻¹σ(2)`. -/
def swapEnds (k j : ℕ) : ℕ := if j = 1 then k else if j = k then 1 else j

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    -- `σ(m)` is a permutation of `{1,…,k}`
    (∀ m j : ℕ, 1 ≤ m → m ≤ k → 1 ≤ j → j ≤ k → 1 ≤ sig k m j ∧ sig k m j ≤ k) ∧
    (∀ m i j : ℕ, 1 ≤ m → m ≤ k → 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k →
        sig k m i = sig k m j → i = j) ∧
    -- τ(1) = σ(3) ∘ σ(1) = ρ
    (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 3 (sig k 1 j) = rho k j) ∧
    -- τ(2) = σ(1) ∘ σ(2) = ρ ∘ (k-1, k)
    (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 1 (sig k 2 j) = rho k (swapLast k j)) ∧
    -- σ(2) = σ(1) ∘ (1, k) : Pansiot's pair, transposition at distance 1
    (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 2 j = sig k 1 (swapEnds k j))

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.TauNormalForm
