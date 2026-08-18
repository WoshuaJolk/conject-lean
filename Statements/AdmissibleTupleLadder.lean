import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# AdmissibleTupleLadder — a sharp mod-6 lower bound on `H(k)`, for every `k`

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

Write `H(k)` for the least diameter of an admissible `k`-tuple, where a finite `T ⊆ ℕ` is
**admissible** when every prime `p` omits some residue class `r < p` on `T`.  Since
Goldston–Pintz–Yıldırım, every unconditional bound on `H₁` has the form `H₁ ≤ diam T` for an
admissible `k`-tuple `T`, given the analytic input `DHL[k,2]`.  So `H(k)` is exactly the
**best bound the route can give at parameter `k`**, and a lower bound on `H(k)` is a ceiling
on the route.

## What is proved

An admissible tuple is confined to two residue classes mod 6 (admissibility at 2 leaves three
of the six classes; among `c`, `c + 2`, `c + 4` the residues mod 3 are pairwise distinct, so
admissibility at 3 removes exactly one more).  Consecutive points of such a set are therefore
spaced `2, 4, 2, 4, …`, and any three of them span at least 6.  Iterating:

  `H(k) ≥ 6⌊(k−1)/2⌋ + 2·((k−1) mod 2)`,

stated here as an inequality on the diameter of an arbitrary admissible tuple, with `k` its
cardinality — no separate `H` is defined, so nothing about the *existence* of optimal tuples
is assumed.  The right-hand side runs `0, 2, 6, 8, 12, 14, 18, 20, …` for `k = 1, 2, 3, …`.

## It is sharp for `k ≤ 5`, and that is exhibited, not asserted

`{0,2}`, `{0,2,6}`, `{0,2,6,8}` and `{0,2,6,8,12}` are proved admissible, with cardinalities
`2, 3, 4, 5` and diameters `2, 6, 8, 12` — exactly the bound.  So `H(2) = 2`, `H(3) = 6`,
`H(4) = 8` and `H(5) = 12` are settled here **in both directions**, with no appeal to the
tabulated values.  (The bound first goes slack at `k = 6`, where it gives 14 and the true
value is 16; that is not claimed here.)

## The consequence for the route, made concrete

A separate conjunct instantiates the bound at `k = 50`, Polymath8b's parameter: every
admissible 50-tuple has diameter at least 146.  Read the ladder the other way and it is a
ceiling table for the whole `DHL[k,2] + tuple` route:

* a bound of 4 or better needs `k ≤ 2`, and `DHL[2,2]` at `{0,2}` *is* the twin prime
  conjecture;
* a bound of 6 needs `k ≤ 3`, which is where the conditional GEH record sits;
* a bound of 246 needs `k ≤ 83`.

No amount of searching for narrower tuples can move these, because they are lower bounds on
what any tuple of that size can do.

## What is NOT claimed

Not claimed: any lower bound on `H₁` itself beyond the elementary `H₁ ≥ 2`; `DHL[k,2]` for any
`k`; `H(k)` for `k ≥ 6`, in particular *not* `H(50) ≥ 246`, which is Engelsma's exhaustive
computation and is a far stronger statement than the 146 proved here; and the parity barrier,
which is a heuristic claim about sieves and is logically independent of this, which is a
theorem about tuples.  The answer space of the problem does not move: this is a fact about a
method, and a ceiling is never subtracted.

## The control

`{0,2,4}` is proved **not** admissible.  Without a must-fail case the admissibility predicate
could be satisfiable by everything, and every conjunct above would hold for a void reason.
`{0,2,4}` has the same cardinality as `{0,2,6}` and a smaller diameter, so it is exactly the
set the bound must reject.
-/

namespace Statements.AdmissibleTupleLadder

/-- The canonical proposition.  The mod-6 ladder bound on the diameter of an admissible
tuple; its instantiation at `k = 50`; sharpness witnesses at `k = 2, 3, 4, 5`; and the
must-fail control `{0,2,4}`. -/
abbrev statement : Prop :=
  (∀ (T : Finset ℕ) (lo d : ℕ), (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) →
      6 * ((T.card - 1) / 2) + 2 * ((T.card - 1) % 2) ≤ d)
  ∧ (∀ (T : Finset ℕ) (lo d : ℕ), T.card = 50 → (∀ x ∈ T, lo ≤ x ∧ x ≤ lo + d) →
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) → 146 ≤ d)
  ∧ (({0, 2} : Finset ℕ).card = 2 ∧ (∀ x ∈ ({0, 2} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 2) ∧
      ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2} : Finset ℕ), x % p ≠ r)
  ∧ (({0, 2, 6} : Finset ℕ).card = 3 ∧ (∀ x ∈ ({0, 2, 6} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 6) ∧
      ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6} : Finset ℕ), x % p ≠ r)
  ∧ (({0, 2, 6, 8} : Finset ℕ).card = 4 ∧
      (∀ x ∈ ({0, 2, 6, 8} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 8) ∧
      ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6, 8} : Finset ℕ), x % p ≠ r)
  ∧ (({0, 2, 6, 8, 12} : Finset ℕ).card = 5 ∧
      (∀ x ∈ ({0, 2, 6, 8, 12} : Finset ℕ), 0 ≤ x ∧ x ≤ 0 + 12) ∧
      ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 6, 8, 12} : Finset ℕ), x % p ≠ r)
  ∧ ¬ (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ ({0, 2, 4} : Finset ℕ), x % p ≠ r)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.AdmissibleTupleLadder
