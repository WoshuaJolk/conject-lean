import Mathlib

namespace Statements.PlyGridOptimal

/-- **Du–McCarty Problem 5.2: is the fine grid optimal?**

Du and McCarty (*A survey of degree-boundedness*, European J. Combin. 2024, §5.1) prove
(Lemma 5.1) that for any positive integers `k, d` and any finite `k`-thin collection `B` of
balls in `ℝ^d`, the intersection graph `G(B)` has a vertex of degree less than `k * 3 ^ d`,
and ask (Problem 5.2) for the smallest integer `c_d` such that every finite `k`-thin
collection of balls in `ℝ^d` contains a ball meeting at most `c_d * k + O_d(1)` others. They
remark that a very fine grid ought to show `c_d` is exponential, which is the construction
giving the value `2 ^ d`.

This is the statement that `c_d ≤ 2 ^ d`: that the grid value is admissible, i.e. that
`2 ^ d` may replace Du–McCarty's `3 ^ d` in Lemma 5.1 up to an additive `O_d(1)`.

Read-back, term by term.
* `C : ℕ → ℕ` quantified **outermost** is the `O_d(1)`: the additive slack may depend on the
  dimension `d` and on nothing else. In particular it may not depend on `k` or on the family,
  which is what stops the statement from being trivially true.
* `x : Fin n → EuclideanSpace ℝ (Fin d)` and `r : Fin n → ℝ` with `∀ i, 0 < r i` is a finite
  collection of `n` closed balls of positive radius; `Function.Injective (fun i => (x i, r i))`
  makes it a *collection* (a set of balls) rather than a multiset, matching the source.
* `0 < n` because the conclusion asserts that the collection *contains* a ball; the empty
  collection contains none.
* `k`-thin is the source's own definition, "every point of the ground set is in at most `k`
  elements of `B`", read on the ground set `ℝ^d`.
* The conclusion counts the balls of the collection **other than** `i₀` that meet ball `i₀`,
  i.e. the degree of `i₀` in the intersection graph `G(B)`, exactly as in Lemma 5.1.

The statement quantifies over all `k` and all `n`; both bounds in the literature are
`2 ^ (d-1) ≤ c_d ≤ 3 ^ d`, so this proposition is open, and it may be false: the campaign
bound `c_d ≤ ρ_d = Θ(2 ^ d √d)` leaves a factor `Θ(√d)` of room above `2 ^ d`. A refutation
is a scalable family, in one fixed dimension, whose every member has degree exceeding
`2 ^ d * k + C` for every constant `C`. -/
abbrev statement : Prop :=
  ∃ C : ℕ → ℕ,
    ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
      ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        Function.Injective (fun i => (x i, r i)) →
        (∀ p : EuclideanSpace ℝ (Fin d),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀ : Fin n,
          {i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
            ≤ 2 ^ d * k + C d

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PlyGridOptimal
