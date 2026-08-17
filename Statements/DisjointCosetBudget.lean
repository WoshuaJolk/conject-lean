import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# DisjointCosetBudget — the counting core of the `B = ∅` case

The load-bearing step of the group-invariant route to Lemma C. In an exact coset cover of
`G \ {e}` the hole `{e}` sits inside every used subgroup `K`, so `K` itself is never a used
part; the used cosets of `K` that lie inside a subgroup `M`, together with `K`, are pairwise
disjoint cosets of `K` inside `M`. That is the whole content of Theorem 3.4 once the mass
identity has reduced `t_0 + 1` to `|M|`.

This module is the single source of truth for what the statement means; a submission proves
it in its own module and the verifier bridges the two.
-/

namespace Statements.DisjointCosetBudget

/-- The canonical proposition. `G` is a finite group, `K ≤ M` are subgroups, and `C` is a
finite family of pairwise distinct left cosets of `K` (elements of `G ⧸ K`), each of which
has a representative in `M`, and none of which is the coset of `1`. Then `C` together with
`K` itself fits inside `M`:

`(C.card + 1) * Nat.card K ≤ Nat.card M`. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K M : Subgroup G), K ≤ M →
    ∀ C : Finset (G ⧸ K),
      (∀ q ∈ C, ∃ g : G, g ∈ M ∧ q = (g : G ⧸ K)) →
      ((1 : G) : G ⧸ K) ∉ C →
      (C.card + 1) * Nat.card K ≤ Nat.card M

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.DisjointCosetBudget
