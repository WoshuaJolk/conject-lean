import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# TwinPrimesSmallCases — the concrete twin-prime data, pinned by the kernel

Self-contained: imports only `Mathlib`, mentions only `Nat.Prime`, `Finset`, and numerals,
uses no `Commons`.

## What is claimed, and what is not

Nothing asymptotic and nothing about infinitude.  Every conjunct below is a closed
arithmetical fact that Lean's kernel settles by computation.  **This statement bounds
nothing about `H_1` and is not progress on the problem.**  Its purpose is different and
narrow: the canonical statement of problem 9 reads

    `∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)`

and a reader has to take on trust that `Nat.Prime p ∧ Nat.Prime (p + 2)` says "`p` and
`p + 2` are twin primes".  A mis-stated primality predicate, an off-by-one in the `+ 2`, or
a shifted bound in the `N <` would all leave a statement that still looks right on the page.
Here they do not: each such slip makes one of the conjuncts below **false**, and the kernel
refuses it.

## Read-back, term by term

* **The exact list below 100.**  The twin-prime lower members `p < 100` are exactly
  `3, 5, 11, 17, 29, 41, 59, 71`, and there are `8` of them.  Note `5` occurs as a lower
  member of `(5, 7)` even though it is the upper member of `(3, 5)`: the predicate is
  "`p` and `p + 2` are both prime", not "`p` starts a maximal twin block".
* **The count below 200 is 15.**  A second, independent bound, so that an error in the
  filter that happened to preserve the first count would still have to preserve this one.
* **`3` is least.**  No `p < 3` has `p` and `p + 2` both prime; in particular the pair
  `(2, 4)` is not admitted, which is what fixes the base of the list.
* **The `+ 2` is really `+ 2`.**  `Nat.Prime 7` holds and `Nat.Prime 9` does not, so `(7, 9)`
  is not a pair; and the `p, p + 1` variant of the same filter over the same range collapses
  to the single value `2`, while the `p, p + 4` (cousin prime) variant has `9` elements
  rather than `8`.  An off-by-one in the offset therefore cannot survive.
* **Witnesses above `10 ^ 5` and `10 ^ 6`.**  `(100151, 100153)` and `(1000037, 1000039)`.
  These discharge the body of the canonical proposition at `N = 100000` and `N = 1000000`,
  which is what makes it satisfiable at all; they say nothing about any larger `N`.

## Precedent

Modelled on `PaleyLocSmallCases` (problem 7): a small-cases anchor whose value is that a
mis-statement is caught by the kernel rather than by a reader.
-/

namespace Statements.TwinPrimesSmallCases

/-- The canonical proposition: the concrete twin-prime data below 200, the guards that fix
the offset `+ 2`, and two explicit twin pairs above `10 ^ 5` and `10 ^ 6`.  Everything is
decidable or a named numeral witness; nothing is asymptotic. -/
abbrev statement : Prop :=
  -- the exact list of twin-prime lower members below 100, and its size
  ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
      = ({3, 5, 11, 17, 29, 41, 59, 71} : Finset ℕ))
  ∧ ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card = 8
  -- an independent second count, below 200
  ∧ ((Finset.range 200).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card = 15
  -- 3 is the least lower member: (0, 2), (1, 3), (2, 4) are all excluded
  ∧ (∀ p ∈ Finset.range 3, ¬ (Nat.Prime p ∧ Nat.Prime (p + 2)))
  -- the offset is exactly 2: (7, 9) is not a pair
  ∧ (Nat.Prime 7 ∧ ¬ Nat.Prime 9)
  -- and the neighbouring offsets 1 and 4 give visibly different answers on the same range
  ∧ ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 1)) = ({2} : Finset ℕ))
  ∧ ((Finset.range 100).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 4))).card = 9
  -- explicit witnesses above 10 ^ 5 and 10 ^ 6
  ∧ (∃ p : ℕ, 100000 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
  ∧ (∃ p : ℕ, 1000000 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesSmallCases
