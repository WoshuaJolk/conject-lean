import Commons.SetPairSystem
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Card

/-!
# FibreCountIdentity — an exact identity satisfied by every 1-cross intersecting SPS

Fix an `(a,b)`-bounded `1`-cross intersecting set pair system `(A, B)` of size `m`, and for
a ground element `e` write `T e := {j | e ∈ B j}` for the set of indices whose `B`-side
contains `e`.  Fix any index `i`.  Then the sets `T e` with `e ∈ A i`

* avoid `i`, because `A i ∩ B i = ∅`;
* are pairwise disjoint, because `|A i ∩ B j| = 1` forbids two elements of `A i` from
  lying in the same `B j`;
* cover everything else, because `|A i ∩ B j| = 1` produces one for each `j ≠ i`.

So they partition `Fin m \ {i}` and their cardinalities sum to `m - 1`.  Written without
truncated subtraction:

    (∑ e ∈ A i, |T e|) + 1 = m,     for EVERY index i.

This is an equality, not a bound, and it holds simultaneously at every index.  It is the
engine behind two further statements on this problem: the ground-degree ceiling (bounded
`T`-sizes force `m ≤ a·t + 1`) and the dual peeling recursion.

`T` is supplied as data together with its defining property, so the proposition carries no
`Decidable` instance and no `Finset.filter`.
-/

namespace Statements.FibreCountIdentity

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (a b m : ℕ) (A B : Fin m → Finset ℕ) (T : ℕ → Finset (Fin m)),
    Commons.OneCrossSPS a b m A B →
    (∀ (e : ℕ) (j : Fin m), j ∈ T e ↔ e ∈ B j) →
    ∀ i : Fin m, (∑ e ∈ A i, (T e).card) + 1 = m

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.FibreCountIdentity
