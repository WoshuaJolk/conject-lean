import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic

/-!
# TwoPowerBinaryUniqueness

A multiset of exactly `d` natural-number exponents whose powers of two sum to `2 ^ d - 1`
is exactly `{0, 1, …, d-1}`.

This is the arithmetic heart of `ExpLatticeFactorialLower` (`h(L_d(2)) ≥ d!`).  The `d!`
permutations of `(2⁰, …, 2^(d-1))` all lie on the hyperplane `Σ xᵢ = 2^d - 1`, so the convex
hull of the permutohedron lies inside that hyperplane, and a lattice point of `L_d(2)` in
the hull is a `d`-tuple of powers of two summing to `2^d - 1`.  The statement below says
that such a tuple is a permutation of `(2⁰, …, 2^(d-1))` and nothing else, which is exactly
the emptiness half of that construction.

Equivalently: among multisets of powers of two with a given sum, the binary representation
is the unique one of minimum size.  Merging a repeated exponent (`2^a + 2^a = 2^(a+1)`)
preserves the sum and drops the count by one, so a multiset with a repeat is never minimal.
-/

namespace Statements.TwoPowerBinaryUniqueness

/-- A multiset of exactly `d` exponents whose powers of two sum to `2 ^ d - 1` is
`{0, 1, …, d-1}`. -/
abbrev statement : Prop :=
  ∀ (d : ℕ) (s : Multiset ℕ), Multiset.card s = d →
    (s.map (fun i => 2 ^ i)).sum = 2 ^ d - 1 → s = Multiset.range d

/-- The target.  A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.TwoPowerBinaryUniqueness
