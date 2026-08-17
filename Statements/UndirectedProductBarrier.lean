import Mathlib.Data.Real.Archimedean

/-!
# UndirectedProductBarrier — the direct-product route to Currie–Mol Conjecture 1 is dead

Currie–Mol's own Theorem 6 builds an undirected-power-free word by taking a *direct product*
(letterwise pairing) of a word over `Σ_{k₁}` with a word over `Σ_{k₂}`, giving a word over an
alphabet of size `k₁ · k₂`. The bridge, which is why this arithmetic statement is the
elimination:

* if `w = u ⊗ v` letterwise, then every ordinary repetition of period `p` in `w` is
  simultaneously a repetition of period `p` in `u` and in `v`; so `w` is ordinary
  `α⁺`-free as soon as **one** of `u`, `v` is;
* an infinite word over `Σ_m` that is ordinary `α⁺`-free exists only if `α ≥ RT(m)`, and
  Dejean's *lower* bound — the elementary half, proved for every `m` — gives
  `RT(m) ≥ m/(m-1)`;
* so a product construction over `k = k₁·k₂` letters can reach the undirected threshold
  `(k-1)/(k-2)` only if `k_i/(k_i-1) ≤ (k-1)/(k-2)` for some factor `k_i`.

This statement says that never happens for a nontrivial factorisation: **both** factors'
Dejean lower bounds strictly exceed `(k-1)/(k-2)`, for every `k ≥ 4` and every splitting
`k = k₁ · k₂` with `k₁, k₂ ≥ 2`. Hence no nontrivial direct product over exactly `k` letters
can witness the conjectured upper bound, at any `k` — the route is dead uniformly, not just
for large `k`.

Elementary content: after clearing denominators (`k₁ - 1 ≥ 1` and `k - 2 ≥ 2` are positive),
`k₁/(k₁-1) > (k-1)/(k-2)` is equivalent to `k₁ < k - 1`, and `k = k₁k₂` with `k₂ ≥ 2` forces
`k₁ ≤ k/2 ≤ k - 2`.

Verified independently in exact rational arithmetic (`fractions.Fraction`, no floats) for
every `k` in `4 … 3999` and every factorisation, in both the rational and the integer form.
-/

namespace Statements.UndirectedProductBarrier

/-- The canonical proposition: for every `k ≥ 4` and every factorisation `k = k₁ · k₂` into
factors `≥ 2`, both Dejean lower bounds `kᵢ/(kᵢ-1)` strictly exceed the undirected target
`(k-1)/(k-2)`. -/
abbrev statement : Prop :=
  ∀ k k₁ k₂ : ℕ, 4 ≤ k → 2 ≤ k₁ → 2 ≤ k₂ → k = k₁ * k₂ →
    ((k : ℝ) - 1) / ((k : ℝ) - 2) < (k₁ : ℝ) / ((k₁ : ℝ) - 1) ∧
    ((k : ℝ) - 1) / ((k : ℝ) - 2) < (k₂ : ℝ) / ((k₂ : ℝ) - 1)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UndirectedProductBarrier
