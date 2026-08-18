import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# TwinPrimeSingularSeries — the twin-prime singular series is bounded away from zero

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## Why this belongs to this problem

The Hardy–Littlewood conjecture predicts `π₂(x) ~ C₂ · x / (log x)²` with the **twin prime
constant** `C₂ = 2 ∏_{p ≥ 3 prime} (1 − 1/(p−1)²)`.  `C₂` is the *singular series* of the
pattern `{0, 2}`: the product over primes of the local densities, `(1 − 2/p)/(1 − 1/p)²` for
odd `p` and `2` for `p = 2`.  The whole predictive content of the conjecture rests on
`C₂ > 0`, and `C₂ > 0` is precisely the quantitative form of "the pattern `(n, n+2)` is not
locally obstructed": each individual factor is positive because `{0, 2}` misses a class mod
`p`, but positivity of an infinite product of numbers `< 1` is a convergence statement and
does not follow factor by factor.  If the product diverged to `0`, the local data would
predict density zero and the conjecture would lose its motivation.

The board already carries the qualitative fact — `{0, 2}` is admissible at every prime, and
no covering congruence removes the pattern.  That statement explicitly lists "the
Hardy–Littlewood singular series and its positivity as a convergent product" as *out of
scope*.  This statement supplies it, elementarily and with an explicit constant.

## What is proved

* **A uniform positive lower bound.**  For every `N`, the truncated product over the odd
  primes at most `N` is at least `1/4`.  Uniform in `N`, so it survives the limit: the
  infinite product cannot be `0`, and `C₂ ≥ 1/2`.
* **An upper bound of 1**, since every factor lies in `(0, 1]`.  Together with the first
  conjunct the truncations are confined to `[1/4, 1]`.
* **A numerical read-back**: at `N = 10` the product is exactly `175/256`.  This pins the
  indexing — the factors are those for `p = 3, 5, 7` and no others, with `(1 − 1/(p−1)²)` and
  not `(1 − 1/p²)` or `(1 − 2/p)`.  An off-by-one in the range or a wrong local density would
  change this rational number.

The true value is `∏ ≈ 0.66016`, so `C₂ ≈ 1.32032`; `1/4` is a comfortable, honest bound and
is not claimed to be sharp.

## The argument

Elementary, with no analytic input.  For an odd prime `p`, the factor is `1 − a_p` with
`a_p = 1/(p−1)² ∈ (0, 1]`.  Weierstrass's inequality gives `∏ (1 − a_p) ≥ 1 − ∑ a_p`, so it
suffices that `∑_{p ≥ 3} 1/(p−1)² ≤ 3/4`.  Dropping primality and summing over **all**
integers `n ≥ 3` only increases the sum, and `∑_{n ≥ 3} 1/(n−1)² = 1/4 + ∑_{j ≥ 3} 1/j²`,
where the tail telescopes against `1/(j−1) − 1/j` to at most `1/2`.  So the sum is at most
`3/4` and the product at least `1/4`.  No Mertens theorem, no prime number theorem, and no
infinite-product machinery is used; the bound is uniform in `N` by construction.

## What is NOT claimed

Not claimed: the Hardy–Littlewood asymptotic itself, or any upper or lower bound on the
number of twin primes; the exact value of `C₂`; that the truncations converge (they do, being
antitone and bounded, but that is not stated here); sharpness of `1/4`; and anything about
`H₁`.  The answer space of the problem does not move.  This makes a premise of the standard
heuristic checkable rather than assumed, and it is not evidence that the conjecture is true.
-/

namespace Statements.TwinPrimeSingularSeries

/-- The canonical proposition.  The truncated twin-prime singular series (without its factor
of 2) is at least `1/4` and at most `1` for every truncation point, and equals `175/256` at
`N = 10`. -/
abbrev statement : Prop :=
  (∀ N : ℕ, (1 : ℝ) / 4 ≤
      ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2))
  ∧ (∀ N : ℕ,
      ∏ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1)
  ∧ (∏ p ∈ (Finset.range (10 + 1)).filter (fun p => Nat.Prime p ∧ 3 ≤ p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2)) = 175 / 256

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimeSingularSeries
