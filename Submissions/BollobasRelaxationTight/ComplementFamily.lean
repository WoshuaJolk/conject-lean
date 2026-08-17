import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.EquivFin
import Commons.SetPairSystem

/-!
Route: Bollobás' own extremal family, indexed explicitly.

Take the ground set `[2n] = Finset.range (2 * n)` and let `sset n` be its `n`-subsets, so
`(sset n).card = (2n).choose n` by `Finset.card_powersetCard`.  Transport an index
`i : Fin ((2n).choose n)` through `Finset.equivFin` to get the `i`-th `n`-subset `F n i`,
and set `A i = F n i`, `B i = range (2n) \ F n i`.

* `|A i| = n` and `|B i| = 2n - n = n`;
* `A i ∩ B i = ∅`, the second being the complement of the first inside the ground set;
* for `i ≠ j` the sets `F n i` and `F n j` are DISTINCT `n`-subsets, so neither contains the
  other (equal cardinality forbids proper containment), hence `F n i \ F n j ≠ ∅`, and any
  element of it lies in `A i ∩ B j`.

So the `Nonempty` cross clause is attained at `(2n).choose n` for every `n`: Bollobás' bound
is tight for the relaxation, and the exactly-one refinement is doing all the work in the
root problem.
-/

namespace Submissions.BollobasRelaxationTight.ComplementFamily

open Finset

/-- The `n`-subsets of the ground set `[2n]`. -/
private def sset (n : ℕ) : Finset (Finset ℕ) := (Finset.range (2 * n)).powersetCard n

private lemma sset_card (n : ℕ) : (sset n).card = (2 * n).choose n := by
  rw [sset, Finset.card_powersetCard, Finset.card_range]

/-- The `i`-th `n`-subset of `[2n]`. -/
private noncomputable def E (n : ℕ) : Fin ((2 * n).choose n) ≃ {x // x ∈ sset n} :=
  (Finset.equivFinOfCardEq (sset_card n)).symm

private noncomputable def F (n : ℕ) (i : Fin ((2 * n).choose n)) : Finset ℕ := (E n i : Finset ℕ)

private lemma F_mem (n : ℕ) (i : Fin ((2 * n).choose n)) : F n i ∈ sset n := (E n i).2

private lemma F_subset (n : ℕ) (i : Fin ((2 * n).choose n)) : F n i ⊆ Finset.range (2 * n) :=
  (Finset.mem_powersetCard.1 (F_mem n i)).1

private lemma F_card (n : ℕ) (i : Fin ((2 * n).choose n)) : (F n i).card = n :=
  (Finset.mem_powersetCard.1 (F_mem n i)).2

private lemma F_inj (n : ℕ) : Function.Injective (F n) := fun _ _ hij =>
  (E n).injective (Subtype.ext hij)

/-- The canonical proposition of `Statements.BollobasRelaxationTight`. -/
theorem proof :
    ∀ n : ℕ, ∃ A B : Fin ((2 * n).choose n) → Finset ℕ,
      (∀ i, (A i).card ≤ n) ∧
      (∀ i, (B i).card ≤ n) ∧
      (∀ i, A i ∩ B i = ∅) ∧
      (∀ i j, i ≠ j → (A i ∩ B j).Nonempty) := by
  intro n
  classical
  refine ⟨F n, fun i => Finset.range (2 * n) \ F n i, ?_, ?_, ?_, ?_⟩
  · intro i; exact le_of_eq (F_card n i)
  · intro i
    have hin : F n i ∩ Finset.range (2 * n) = F n i := Finset.inter_eq_left.2 (F_subset n i)
    rw [Finset.card_sdiff, Finset.card_range, hin, F_card n i]
    omega
  · intro i
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and]
    tauto
  · intro i j hij
    have hne : F n i ≠ F n j := fun h => hij (F_inj n h)
    have hnsub : ¬ (F n i ⊆ F n j) := by
      intro hsub
      exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [F_card, F_card]))
    obtain ⟨x, hxi, hxj⟩ := Finset.not_subset.1 hnsub
    exact ⟨x, Finset.mem_inter.2 ⟨hxi, Finset.mem_sdiff.2 ⟨Finset.mem_of_subset (F_subset n i) hxi, hxj⟩⟩⟩

end Submissions.BollobasRelaxationTight.ComplementFamily
