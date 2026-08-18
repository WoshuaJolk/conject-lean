import Mathlib

namespace Statements.PlyUpperTwoPowD

/-- **`c_d = O(d · 2^d)` in Du–McCarty Problem 5.2: the exponential rate of `c_d` is `2`.**

Du and McCarty (*A survey of degree-boundedness*, European J. Combin. 2024, §5.1, Lemma 5.1)
prove that every finite `k`-thin collection of balls in `ℝ^d` contains a ball meeting fewer
than `k · 3 ^ d` others, and ask (Problem 5.2) for the smallest `c_d` that can replace `3 ^ d`
up to an additive `O_d(1)`. This statement is `c_d ≤ 16 · d · 2 ^ d`, with additive constant
`0`, which pins the exponential rate `limsup_d log₂(c_d)/d` at its lower bound `1`: the
published `3 ^ d` had rate `log₂ 3 = 1.5849…`.

Route, in full, so it can be checked without the Lean.

1. *Min-radius reduction (Du–McCarty).* Take a ball `B(x₀, r₀)` of minimum radius. Each
   neighbour `B(xᵢ, rᵢ)` has `rᵢ ≥ r₀` and `‖xᵢ - x₀‖ ≤ rᵢ + r₀`, so it contains a ball of
   radius `r₀` whose centre `pᵢ` satisfies `‖pᵢ - x₀‖ ≤ 2 r₀` (slide the centre towards `x₀`
   by `min(rᵢ - r₀, ‖xᵢ - x₀‖)`). Sub-balls preserve `k`-thinness. Rescaling by `r₀`, the
   degree of `B(x₀, r₀)` is at most the number `m` of unit balls with centres in `B(0,2)`
   that can be `k`-thin.

2. *Test set `B(0, √3)`.* For any `q` with `‖q‖ ≤ 2`, the cap
   `Cₑ = {u : ‖u‖ ≤ 1, ⟪e, u⟫ ≤ -1/2}` with `e = q/‖q‖` satisfies `q + Cₑ ⊆ B(q,1) ∩ B(0,√3)`,
   because `‖q + u‖² ≤ s² - s + 1 ≤ 3` for `s = ‖q‖ ≤ 2`. Integrating the counting function
   over `B(0,√3)` gives `m · vol(C) ≤ k · 3^{d/2} · v_d`, where `v_d = vol(B(0,1))` and
   `vol(C) = vol(Cₑ)` by rotation invariance. The radius `√3` is optimal: writing
   `h = (5 - R²)/4` for the cap height forced by `R`, the exponential rate of
   `R^d / (1-h²)^{(d-1)/2}` is `4R²/((R²-1)(9-R²))` under the square root, minimised at
   `R² = 3` with value exactly `4`, i.e. rate exactly `2`.

3. *A lower bound for the cap.* The ellipsoid `-c·e₀ + diag(α, β, …, β)(B(0,1))` with
   `α = 1/(8d)`, `c = 1/2 + α` and `β² = 3/4 - 3α` lies inside `C`: its `e₀`-coordinate is at
   most `-c + α = -1/2`, and `(c - αt)² + β²(1-t²) ≤ 1` on `[-1,1]` reduces, after expanding,
   to `(3/4 - 3α - α²)t² + (α + 2α²)t + (2α - α²) ≥ 0`, which follows from `t ≥ -1`, `t² ≥ 0`
   and `α ≤ 1/8` alone. Hence `vol(C) ≥ α β^{d-1} v_d`.

4. *Arithmetic.* `16 d α = 2`, and `4 · 4^d · (β²)^{d-1} = 16 · 3^{d-1} · (1 - 1/(2d))^{d-1}
   ≥ 8 · 3^{d-1} ≥ 3^d` by Bernoulli, which is `(√3^d)² ≤ (2 · 2^d · β^{d-1})²`. So
   `m ≤ 16 · d · 2^d · k`. The sharp form of this argument gives `4√6 ≈ 9.8` in place of `16`.

Read-back, term by term.
* All dimensions `d ≥ 1` at once, all `k`, all finite families of `n ≥ 1` balls of positive
  radius; the bound `16 * d * 2 ^ d * k` has **no additive slack**, so it is stronger than the
  `c_d k + O_d(1)` shape Problem 5.2 asks about.
* No injectivity of `fun i => (x i, r i)` is assumed, so multisets of balls are covered too;
  this is a strengthening relative to `Statements.PlyGridOptimal`, whose antecedent has that
  hypothesis.
* `k`-thin is the source's own definition read on the ground set `ℝ^d`, and the conclusion
  counts the members **other than** `i₀` meeting `i₀`, i.e. degree in the intersection graph
  `G(B)` of Lemma 5.1, with the set-level adjacency the problem's schema fixes.

Relation to the neighbouring statements. This is weaker than
`Statements.PlyUpperTwoPowSqrt` (which asks for `K · 2^d · √d`, a factor `√d` sharper) and
weaker than `Statements.PlyGridOptimal` (the root, `2^d` with additive slack). It is stronger
than `Statements.PlyDegreeGaussian` in rate: that statement's `√5 = 2.236…` per dimension is
the exact ceiling of the Gaussian dual, and this argument passes it by using the cap shape
that the Gaussian's reflection-symmetry step throws away. It does **not** settle the root:
`Statements.PlyShellBarrier` says the min-radius reduction used here ceilings at
`Θ(2^d √d) > 2^d`, and this proof is inside that reduction, so `16 d 2^d` cannot be pushed
below `2^d` by sharpening any constant in it. -/
abbrev statement : Prop :=
  ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
      (∀ i, 0 < r i) →
      (∀ p : EuclideanSpace ℝ (Fin d),
          {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
      ∃ i₀ : Fin n,
        {i : Fin n | i ≠ i₀ ∧
            (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
          ≤ 16 * d * 2 ^ d * k

/-- The open target. A submission proves `statement` in its own module and the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.PlyUpperTwoPowD
