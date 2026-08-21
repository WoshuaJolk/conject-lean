import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Finset.Card

/-!
# UPBFromDegreeBudget — unextendibility is a budget, and nothing else

Every unextendibility proof in this corner of the subject is a case analysis: enumerate how a
candidate product vector could annihilate the states, and rule the cases out. `MinUPB344`'s
witness on `jig.so/p/13` needs a pruned analysis over parallel classes of its `C^3` factor;
`MinUPB224kMinus1`'s on `jig.so/p/6` needs one over the parallel classes of two qubit factors.
Both analyses are bespoke, and neither survives a change of dimensions.

This statement replaces them with a count. Call the number of states a single nonzero local
vector `a` can annihilate in factor `j` the *killing number* of that factor, and suppose it is
bounded by `c j`. If the killing numbers sum to less than the number of states, then no product
vector can annihilate all of them, because a product vector is annihilated by a state only if
some factor pairing vanishes, so the states killed by a candidate are covered by `p` sets of
sizes `c 1, …, c p`, and `Σⱼ cⱼ < m` leaves a survivor.

That is the whole content, and it is the reason the root question
`MinUPBAtMostTrivialPlusOne` is a design problem rather than a search:

* a family in **general position** in factor `j` — every `dⱼ` of its local vectors independent —
  has killing number at most `dⱼ − 1`, since the annihilated vectors lie in a hyperplane;
* so `p` general-position factors give `Σⱼ (dⱼ − 1) = f_N − 1 < f_N`, and any `f_N` pairwise
  orthogonal product states with all factors in general position are automatically a UPB;
* one factor allowed **one unit of degeneracy** — killing number `dⱼ` instead of `dⱼ − 1`, i.e.
  some `dⱼ` of its local vectors dependent, but never `dⱼ + 1` in a hyperplane — gives
  `Σⱼ cⱼ = f_N < f_N + 1 = m`, which is exactly the budget a minimum UPB of size `f_N + 1`
  needs.

One unit is also the most that can be spent: `GenPosUPBTrivialCeiling` (`jig.so/p/14?s=2`) shows
general position alone caps a pairwise-orthogonal family at `f_N`, and the same count shows a
family of `f_N + 1` states must be tight in every factor at every state. So the budget clause
below is not one sufficient condition among many; it is the shape every witness for this problem
must have, and supplying it is all that is left after the orthogonality graphs are chosen.

## Reading the formalisation

Conventions are the root's: a product state is its list of factors, the inner product is the
standard Hermitian one written open-coded and conjugate-linear in the first slot, and the
conclusion is the root's unextendibility clause verbatim, `∃ i` innermost.

The killing-number hypothesis is phrased over an arbitrary `Finset` of states rather than as the
cardinality of a filtered set, so that no decidability instance is needed and a submission need
not match one: `∀ S, (∀ i ∈ S, ⟨vᵢⱼ | a⟩ = 0) → S.card ≤ c j` says exactly that at most `c j`
states are annihilated by `a` in factor `j`.

Neither nonzero-ness of the states nor pairwise orthogonality appears: this is the
unextendibility half alone, and it holds without them. A caller supplies those separately to get
a UPB. `m` and `p` are arbitrary naturals, `d` and `c` arbitrary, with no admissibility
hypothesis of any kind.
-/

namespace Statements.UPBFromDegreeBudget

abbrev statement : Prop :=
  ∀ p m : ℕ, ∀ d : Fin p → ℕ, ∀ c : Fin p → ℕ,
    ∀ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
    (∑ j, c j) < m →
    (∀ j : Fin p, ∀ a : Fin (d j) → ℂ, a ≠ 0 →
      ∀ S : Finset (Fin m), (∀ i ∈ S, (∑ r, star (v i j r) * a r) = 0) → S.card ≤ c j) →
    ∀ a : (j : Fin p) → Fin (d j) → ℂ, (∀ j, a j ≠ 0) →
      ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0

theorem target : statement := sorry

end Statements.UPBFromDegreeBudget
