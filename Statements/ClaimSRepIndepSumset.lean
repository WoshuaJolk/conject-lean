import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.BigOperators

/-!
# ClaimSRepIndepSumset — the representative-independent sumset strengthening

For every exact coset cover of `G` with a hole at the identity, and for EVERY choice of one
representative from each used coset, the sets `S_i = {1} ∪ {representatives of H i's used
cosets}` satisfy `S_1 * ... * S_r = G`. Since `|S_i| = c_i + 1`, this implies Lemma C.

SCOPE WARNING: same group-invariant boundary as Lemma C. Not the posed problem.
-/

namespace Statements.ClaimSRepIndepSumset

/-- The `p`-th part, written without pointwise-set machinery: the left coset
`rep p • H p.1 = {x | (rep p)⁻¹ * x ∈ H p.1}`. -/
def part {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) (p : (i : Fin r) × Fin (c i)) : Set G :=
  {x : G | (rep p)⁻¹ * x ∈ H p.1}

/-- An exact coset cover of `G` with a single hole at the identity. `H` is injective, so the
`H i` are the DISTINCT used subgroups and `c i` is the multiplicity of `H i`. The parts avoid
the identity, are pairwise disjoint, and together with the hole `{1}` they cover `G`. -/
def IsHoleCover {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) : Prop :=
  Function.Injective H ∧
  (∀ p, (1 : G) ∉ part H c rep p) ∧
  (∀ p q, p ≠ q → Disjoint (part H c rep p) (part H c rep q)) ∧
  (⋃ p, part H c rep p) ∪ {1} = Set.univ

/-- CLAIM S. `S_i * ... * S_r = G`, written as: every `g` factors with one factor from each
`S_i = {1} ∪ {s ⟨i, j⟩}`. -/
abbrev statement : Prop :=
  ∀ (G : Type) [CommGroup G] [Finite G] (r : ℕ) (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G),
    IsHoleCover H c rep →
      ∀ s : ((i : Fin r) × Fin (c i)) → G, (∀ p, s p ∈ part H c rep p) →
        ∀ g : G, ∃ t : Fin r → G,
          (∀ i, t i = 1 ∨ ∃ j : Fin (c i), s ⟨i, j⟩ = t i) ∧ (∏ i, t i) = g

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ClaimSRepIndepSumset
