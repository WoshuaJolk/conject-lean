import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# TauBlockSwapParity — at `k ≡ 2 (mod 4)` the Currie–Mol group is imprimitive, forcing odd `r`

Currie–Mol's Theorem 5 settles a value of `k` by exhibiting an `r`-uniform binary morphism `f`
with the Moulin-Ollagnier algebraic property `∃ φ ∈ S_k, φ · τ(f(a)) · φ⁻¹ = τ(a)` for
`a ∈ {1,2}`, where `τ = σ ∘ g`. In particular `τ(f(1))` must be **conjugate to `τ(1)`**.

This statement says that for `k ≡ 2 (mod 4)` the group `⟨τ(1), τ(2)⟩` preserves a partition of
the letters into two blocks of size `k/2`, and that **both generators swap the two blocks**:

```
B₁ = {1} ∪ {j : j ≡ 0 or 3 (mod 4)},    B₂ = the complement
```

## The consequence, which is the point

* `τ(1)` is a bijection swapping `B₁` and `B₂` (`TauNormalForm` supplies the bijectivity), so
  `|B₁| = |B₂| = k/2`.
* An element that *preserves* the blocks maps each block into itself, so every one of its cycles
  lies inside a block and has length at most `k/2`.
* `τ(1) = ρ` has cycle type `(k/2 − 1, k/2 + 1)`, and `k/2 + 1 > k/2`. So **anything conjugate to
  `τ(1)` must swap the blocks.**
* Both generators swap, so `τ(u)` swaps exactly when `|u|` is odd.

Therefore: **for every `k ≡ 2 (mod 4)`, a uniform binary morphism with the algebraic property
must have ODD uniformity `r`.** Every even-uniform morphism is ruled out at those `k`, for free,
before any freeness check is run.

## Evidence gathered before stating

The block system was found by computing the minimal block containing `{1, b}` under
`⟨τ(1), τ(2)⟩`: at `k = 22` it is the pair of 11-element blocks above, and at `k = 21, 23, 17, 19`
the group is **primitive** (no nontrivial block system) — this is specifically a phenomenon of
`k ≡ 2 (mod 4)`, absent at `k ≡ 0 (mod 4)` too (`k = 16, 20, 24` are primitive). The closed form,
the swap property for both generators, and `k/2 + 1 > k/2` were checked for every `k ≡ 2 (mod 4)`
in `6 … 58`.

Independent check against the literature, which is what makes this more than a curiosity:
Currie–Mol publish `f_k` for `k = 4 … 21`. Of those, the ones with `k ≡ 2 (mod 4)` are
`k = 6, 10, 14, 18`, with uniformities `7, 25, 21, 21` — **all odd**, as predicted. The only even
uniformities in their entire table are at `k = 8, 13, 20`, none of which is `≡ 2 (mod 4)`.
-/

namespace Statements.TauBlockSwapParity

/-- `ρ`, the step-2 map; identical to `Statements.TauNormalForm.rho`. `τ(1) = ρ`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

/-- The transposition `(k-1, k)`; `τ(2) = ρ ∘ swapLast`. -/
def swapLast (k j : ℕ) : ℕ := if j = k - 1 then k else if j = k then k - 1 else j

/-- Block index of a letter: `0` for `B₁ = {1} ∪ {j ≡ 0, 3 (mod 4)}`, `1` for `B₂`. -/
def blk (j : ℕ) : ℕ :=
  if j = 1 then 0 else if j % 4 = 0 then 0 else if j % 4 = 3 then 0 else 1

/-- The canonical proposition: for `k ≡ 2 (mod 4)`, both `τ(1) = ρ` and `τ(2) = ρ ∘ (k-1,k)`
send every letter to the *opposite* block — `blk` of the image plus `blk` of the source is `1`,
which for a `{0,1}`-valued function says exactly that the block is flipped. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 6 ≤ k → k % 4 = 2 →
    (∀ j : ℕ, 1 ≤ j → j ≤ k → blk (rho k j) + blk j = 1) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k → blk (rho k (swapLast k j)) + blk j = 1)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.TauBlockSwapParity
