import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic

/-!
# KorecSunBarrier — no bound in the total number of parts can imply Lemma C

The Korec / Sun least-`k` line for covering systems produces bounds that are functions of
`k = ∑ cᵢ` alone. Such a bound cannot imply `LemmaCAbelianCosetCover`, because `k` is invariant
under redistributing parts among distinct subgroups while `∏ (cᵢ + 1)` is not — and both
endpoints are realised by actual exact coset covers with a hole at the identity:

* `Z₅` covered by its four non-identity singletons: one used subgroup (the trivial one) with
  `c = (4)`, so `k = 4` and `∏ (cᵢ+1) = 5 = |G|`;
* `Z₁₆` covered by one coset each of the subgroups of order `8, 4, 2, 1` — explicitly the odd
  residues, `{2,6,10,14}`, `{4,12}`, `{8}`, of sizes `8+4+2+1 = 15 = |G| - 1` — so `c = (1,1,1,1)`,
  `k = 4` and `∏ (cᵢ+1) = 16 = |G|`.

Same `k = 4`, products `5` and `16`. So the two bounds are INCOMPARABLE rather than one
refining the other.

`part` and `IsHoleCover` are duplicated verbatim from `Statements.LemmaCAbelianCosetCover`,
because the import allowlist for canonical files does not include `Statements.*`.
-/

namespace Statements.KorecSunBarrier

/-- The `p`-th part: the left coset `rep p • H p.1 = {x | (rep p)⁻¹ * x ∈ H p.1}`. -/
def part {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) (p : (i : Fin r) × Fin (c i)) : Set G :=
  {x : G | (rep p)⁻¹ * x ∈ H p.1}

/-- An exact coset cover of `G` with a single hole at the identity. -/
def IsHoleCover {G : Type} [Group G] {r : ℕ} (H : Fin r → Subgroup G) (c : Fin r → ℕ)
    (rep : ((i : Fin r) × Fin (c i)) → G) : Prop :=
  Function.Injective H ∧
  (∀ p, (1 : G) ∉ part H c rep p) ∧
  (∀ p q, p ≠ q → Disjoint (part H c rep p) (part H c rep q)) ∧
  (⋃ p, part H c rep p) ∪ {1} = Set.univ

/-- The canonical proposition: both endpoints are realised, with the same total `k = 4` and
products `5` and `16`. -/
abbrev statement : Prop :=
  (∃ (r : ℕ) (H : Fin r → Subgroup (Multiplicative (ZMod 5))) (c : Fin r → ℕ)
      (rep : ((i : Fin r) × Fin (c i)) → Multiplicative (ZMod 5)),
        IsHoleCover H c rep ∧ (∑ i, c i) = 4 ∧ (∏ i, (c i + 1)) = 5) ∧
  (∃ (r : ℕ) (H : Fin r → Subgroup (Multiplicative (ZMod 16))) (c : Fin r → ℕ)
      (rep : ((i : Fin r) × Fin (c i)) → Multiplicative (ZMod 16)),
        IsHoleCover H c rep ∧ (∑ i, c i) = 4 ∧ (∏ i, (c i + 1)) = 16)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.KorecSunBarrier
