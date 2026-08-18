import Mathlib

/-!
# GroupInvariantAbelianFGK, proved

Three parts, in one module because a submission is one module.

1. **The recovered Lemma C development**, inlined verbatim from the green artifact
   `ed522efb-032b-4c3d-97e0-2282f6ac8889` on `LemmaCAbelianCosetCover` and renamespaced
   (`derived_from` is declared on this artifact).  It supplies `CosetCover.ExactCosetCover`
   and `ExactCosetCover.lemmaC_holds : |G| <= prod over used subgroups of (c_K + 1)`.
   Its own trailing bridge to the posted `LemmaCAbelianCosetCover` statement is dropped;
   nothing else is changed.

2. **The arithmetic ceiling** (`Arith`), the Finset form of `BlockProductOptimum`: with both
   coordinate sums at most `n`, `prod (u_i v_i + 1) <= 5^(n/2)` for even `n` and
   `2*5^((n-1)/2)` for odd `n`.  Proved through the parity-refined potential
   `25 P^4 <= 5^(p+q) D p D q`, `D t = 5 - t % 2`.

3. **The bridge** (new).  Let `G` be a finite abelian group acting regularly on the index set
   of a `1`-cross intersecting set pair system, with an equivariant ground set `X`.  Write
   `A = A 1`, `B = B 1`.  For `d != 1` the exactness clause `|A 1 cap B d| = 1` says: exactly
   one `x in A` has `d^{-1} . x in B`.  So the sets `{d | d^{-1} . x = y}`, over `x in A` and
   `y in B` in the orbit of `x`, partition `G \ {1}`, and each of them is a LEFT coset of
   `stabilizer G x` -- both facts use commutativity.  That is an exact coset cover with a hole
   at the identity, so Lemma C applies.  The multiplicity of a used subgroup `K` is the number
   of such pairs with `stabilizer x = K`; since stabilisers are constant on orbits, both
   coordinates of every such pair have stabiliser `K`, so that multiplicity is at most
   `alpha K * beta K` where `alpha K = #{x in A : stab x = K}` and `beta K` likewise for `B`.
   The `alpha` sum is `|A| <= n` and the `beta` sum is at most `|B| <= n`, so part 2 finishes it.

Tightness: `G = Z_5`, `X = Z_5` by translation, `A = {0,1}`, `B = {2,4}` is the pentagon and
meets the bound at `n = 2`; `G = Z_25` with a two-orbit ground set (one free orbit, one with
stabiliser of order 5) meets it at `n = 4` with `m = 25`.
-/


/-!
# Recovered formalization of Lemma C, inlined as one module

The whole `CosetCover` development is inlined here and renamespaced under
`Submissions.LemmaCAbelianCosetCover.RecoveredLemmaC`, because a submission is ONE module and
may not import `Statements.*`.  Source order: `Defs`, `SumsetImp`, `Restrict`, `Mass`,
`LemmaD`, `Local`, `Induction`.

The development is ADDITIVE (`AddCommGroup`, hole at `0`, part `= {g | g - base i ∈ sub i}`,
external index type `ι`, `used = image sub univ`, `mult K = |fiber K|`) and concludes
`Fintype.card G ≤ ∏ K ∈ used, (mult K + 1)`.

The posted statement is MULTIPLICATIVE, hole at `1`, parts indexed by
`(i : Fin r) × Fin (c i)` with `H` injective and explicit multiplicities `c`, and concludes
`Nat.card G ≤ ∏ i, (c i + 1)`.  The bridge at the bottom of this file discharges all three
differences.
-/

namespace Submissions.GroupInvariantAbelianFGK.AbelianCosetBridge

-- ======================= inlined: Defs.lean =======================
/-
Hunt3 / CosetCover / Defs.lean — leaf LEAN-0 (W1-5), run 3.

Core objects of the Claim S / Lemma C campaign (hunt/run3/STATE.md §0):
exact coset covers of `G ∖ {0}` with hole `{0}`, used subgroups, multiplicities,
representative choices, the sets `S_H`, and the counting identity.

Design notes (inherited by all later leaves):
* Additive notation throughout: `G : AddCommGroup`, the hole is `0`.
* A cover is indexed by an external type `ι` (one index per part), so the
  restriction construction of Lemma 3.1 (future leaf) is a map on a subtype of `ι`.
* The part at index `i` is the coset `base i + sub i`, encoded by the membership
  predicate `g - base i ∈ sub i`. Both structure axioms are ∀/∧/¬-combinations of
  such memberships, hence Decidable for concrete groups whose subgroups carry
  decidable membership (see Examples.lean for the `decide` controls).
* `Fintype G` is NOT a parameter of the structure; finiteness enters only where a
  cardinality is stated.
-/

namespace CosetCover

/-- A subgroup given by an explicit finset closed under the operations.
Membership is definitionally `g ∈ s`, hence decidable (instance below). -/
def subgroupOfFinset {G : Type*} [AddGroup G] (s : Finset G)
    (h0 : (0 : G) ∈ s) (hadd : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s)
    (hneg : ∀ a ∈ s, -a ∈ s) : AddSubgroup G where
  carrier := s
  zero_mem' := h0
  add_mem' := fun ha hb => hadd _ ha _ hb
  neg_mem' := fun ha => hneg _ ha

instance {G : Type*} [AddGroup G] [DecidableEq G] (s : Finset G) (h0 : (0 : G) ∈ s)
    (hadd : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s) (hneg : ∀ a ∈ s, -a ∈ s) :
    DecidablePred (· ∈ subgroupOfFinset s h0 hadd hneg) :=
  fun g => decidable_of_iff (g ∈ s) Iff.rfl

/-- An exact coset cover of `G ∖ {0}` with hole `{0}` (STATE.md §0): pairwise
disjoint cosets `base i + sub i` whose union is exactly the nonzero elements. -/
structure ExactCosetCover (G : Type*) [AddCommGroup G] (ι : Type*) where
  base : ι → G
  sub : ι → AddSubgroup G
  disj : ∀ i j : ι, i ≠ j → ∀ g : G, ¬(g - base i ∈ sub i ∧ g - base j ∈ sub j)
  covers : ∀ g : G, g ≠ 0 ↔ ∃ i, g - base i ∈ sub i

namespace ExactCosetCover

variable {G : Type*} [AddCommGroup G] {ι : Type*} (P : ExactCosetCover G ι)

theorem base_mem (i : ι) : P.base i - P.base i ∈ P.sub i := by
  rw [sub_self]; exact (P.sub i).zero_mem

theorem base_ne_zero (i : ι) : P.base i ≠ 0 :=
  (P.covers _).mpr ⟨i, P.base_mem i⟩

theorem ne_zero_of_mem {i : ι} {g : G} (h : g - P.base i ∈ P.sub i) : g ≠ 0 :=
  (P.covers g).mpr ⟨i, h⟩

/-- A representative choice: one point in each part (`r i ∈ base i + sub i`). -/
def IsRep (r : ι → G) : Prop := ∀ i, r i - P.base i ∈ P.sub i

/-- The base points themselves are a representative choice. -/
theorem isRep_base : P.IsRep P.base := P.base_mem

theorem rep_ne_zero {r : ι → G} (hr : P.IsRep r) (i : ι) : r i ≠ 0 :=
  P.ne_zero_of_mem (hr i)

section UsedMult

variable [Fintype ι] [DecidableEq (AddSubgroup G)]

/-- The indices of the parts that are cosets of `K`. -/
def fiber (K : AddSubgroup G) : Finset ι :=
  Finset.univ.filter (fun i => P.sub i = K)

/-- The distinct subgroups used by the parts. -/
def used : Finset (AddSubgroup G) := Finset.univ.image P.sub

/-- Multiplicity `c_K`: the number of parts that are cosets of `K`. -/
def mult (K : AddSubgroup G) : ℕ := (P.fiber K).card

variable [DecidableEq G]

/-- `S_K` of Claim S (STATE.md §0): the hole `0` together with the chosen
representatives of the `c_K` used cosets of `K`. -/
def repSet (r : ι → G) (K : AddSubgroup G) : Finset G :=
  insert 0 ((P.fiber K).image r)

theorem card_repSet_le (r : ι → G) (K : AddSubgroup G) :
    (P.repSet r K).card ≤ P.mult K + 1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)

/-- For an honest representative choice, `|S_K| = c_K + 1` exactly: distinct used
cosets give distinct representatives, and `0` lies in no part. -/
theorem card_repSet {r : ι → G} (hr : P.IsRep r) (K : AddSubgroup G) :
    (P.repSet r K).card = P.mult K + 1 := by
  have h0 : (0 : G) ∉ (P.fiber K).image r := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact P.rep_ne_zero hr i hi
  have hinj : Set.InjOn r (P.fiber K) := by
    intro i _ j _ hij
    by_contra hne
    exact P.disj i j hne (r i) ⟨hr i, by rw [hij]; exact hr j⟩
  rw [repSet, Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn hinj, mult]

end UsedMult

section Counting

variable [Fintype G] [∀ i, DecidablePred (· ∈ P.sub i)]

/-- The part at index `i`, as a finset: the coset `base i + sub i`. -/
def partFinset (i : ι) : Finset G :=
  Finset.univ.filter (fun g => g - P.base i ∈ P.sub i)

/-- The subgroup `sub i`, as a finset of `G`. -/
def subFinset (i : ι) : Finset G :=
  Finset.univ.filter (fun g => g ∈ P.sub i)

theorem mem_partFinset {i : ι} {g : G} :
    g ∈ P.partFinset i ↔ g - P.base i ∈ P.sub i := by
  simp [partFinset]

/-- A coset has the cardinality of its subgroup (translate by `g ↦ g - base i`). -/
theorem card_partFinset (i : ι) : (P.partFinset i).card = (P.subFinset i).card := by
  refine Finset.card_nbij' (fun g => g - P.base i) (fun g => g + P.base i)
    ?_ ?_ ?_ ?_
  · intro g hg
    simp_all [partFinset, subFinset]
  · intro g hg
    simp_all [partFinset, subFinset]
  · intro g _
    simp
  · intro g _
    simp

/-- Counting identity (STATE.md §0): `|G| = 1 + Σ_i |H_i|`. -/
theorem counting_identity [DecidableEq G] [Fintype ι] :
    Fintype.card G = 1 + ∑ i : ι, (P.subFinset i).card := by
  classical
  have hdisj : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint P.partFinset := by
    intro i _ j _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro g hgi hgj
    exact P.disj i j hne g ⟨P.mem_partFinset.mp hgi, P.mem_partFinset.mp hgj⟩
  have h0 : (0 : G) ∉ Finset.univ.biUnion P.partFinset := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
    exact P.ne_zero_of_mem (P.mem_partFinset.mp hi) rfl
  have hunion : (Finset.univ : Finset G) = insert 0 (Finset.univ.biUnion P.partFinset) := by
    ext g
    constructor
    · intro _
      rcases eq_or_ne g 0 with rfl | h
      · exact Finset.mem_insert_self 0 _
      · obtain ⟨i, hi⟩ := (P.covers g).mp h
        exact Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, P.mem_partFinset.mpr hi⟩)
    · intro _
      exact Finset.mem_univ g
  calc Fintype.card G
      = (Finset.univ : Finset G).card := Finset.card_univ.symm
    _ = (insert 0 (Finset.univ.biUnion P.partFinset)).card := by rw [← hunion]
    _ = (Finset.univ.biUnion P.partFinset).card + 1 :=
        Finset.card_insert_of_notMem h0
    _ = (∑ i : ι, (P.partFinset i).card) + 1 := by
        rw [Finset.card_biUnion hdisj]
    _ = 1 + ∑ i : ι, (P.subFinset i).card := by
        simp only [P.card_partFinset]; omega

end Counting

end ExactCosetCover

end CosetCover

-- ======================= inlined: SumsetImp.lean =======================
/-
Hunt3 / CosetCover / SumsetImp.lean — P1: Claim S ⟹ Lemma C
(hunt/run3/STATE.md §1 P1; sources 70 §4, re-derived 70b §4a).
-/

namespace CosetCover

open Finset Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Cardinality of an iterated pointwise sumset is at most the product of the
cardinalities: `|Σ_k S_k| ≤ Π_k |S_k|`. -/
theorem card_finsetSum_le {κ : Type*} (T : Finset κ) (f : κ → Finset G) :
    (∑ k ∈ T, f k).card ≤ ∏ k ∈ T, (f k).card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Finset.card_add_le.trans (Nat.mul_le_mul le_rfl ih)

namespace ExactCosetCover

variable {ι : Type*} [Fintype ι] [Fintype G] [DecidableEq (AddSubgroup G)]
variable (P : ExactCosetCover G ι)

/-- **Claim S** (STATE.md §0, source 70 §4): for EVERY representative choice, the
sets `S_K` over the distinct used subgroups sum to all of `G`. -/
def ClaimS : Prop :=
  ∀ r : ι → G, P.IsRep r →
    ∑ K ∈ P.used, P.repSet r K = (Finset.univ : Finset G)

/-- **Lemma C** (STATE.md §0, source 05 App II): `|G| ≤ Π_K (c_K + 1)` over the
distinct used subgroups. -/
def LemmaC : Prop :=
  Fintype.card G ≤ ∏ K ∈ P.used, (P.mult K + 1)

/-- **P1 (Claim S ⟹ Lemma C)**: `|G| = |Σ_K S_K| ≤ Π_K |S_K| ≤ Π_K (c_K + 1)`,
instantiating Claim S at the base-point representatives. -/
theorem lemmaC_of_claimS (hS : P.ClaimS) : P.LemmaC := by
  calc Fintype.card G
      = (Finset.univ : Finset G).card := Finset.card_univ.symm
    _ = (∑ K ∈ P.used, P.repSet P.base K).card := by
        rw [hS P.base P.isRep_base]
    _ ≤ ∏ K ∈ P.used, (P.repSet P.base K).card := card_finsetSum_le _ _
    _ ≤ ∏ K ∈ P.used, (P.mult K + 1) :=
        Finset.prod_le_prod' fun K _ => P.card_repSet_le P.base K

end ExactCosetCover

end CosetCover

-- ======================= inlined: Restrict.lean =======================
/-
Hunt3 / CosetCover / Restrict.lean — Lemma 3.1 (restriction), run 3 wave 2 (leaf 107).

Given an exact coset cover `P` of `G ∖ {0}` and a subgroup `M`, the parts that
meet `M`, intersected with `M`, form an exact coset cover of `M ∖ {0}`
(STATE.md §0, Lemma 3.1; source 70 §3, re-proved 104b §S4(i)).

Also here: the two maximality consequences used downstream (`K ⊔ M = ⊤` for a
coatom `M` and `K ⊄ M`, and the surjectivity of `K → G ⧸ M` it yields), and the
characterization of which parts meet `M`.

Theory files are classical: decidability is supplied by a low-priority local
instance, so no `Decidable` bookkeeping pollutes the statements.
-/

namespace CosetCover

attribute [local instance 10] Classical.propDecidable

variable {G : Type*} [AddCommGroup G]

/-- For a coatom (maximal proper subgroup) `M` and any subgroup `K ⊄ M`,
`K ⊔ M = ⊤`. -/
theorem sup_eq_top_of_not_le {M K : AddSubgroup G} (hM : IsCoatom M) (hK : ¬K ≤ M) :
    K ⊔ M = ⊤ := by
  refine hM.2 _ (lt_of_le_of_ne le_sup_right fun h => hK ?_)
  exact le_sup_left.trans h.symm.le

/-- For a coatom `M` and `K ⊄ M`, the quotient map `G → G ⧸ M` is surjective
already on `K`: every class `j` has a representative in `K`. -/
theorem exists_mk_eq {M K : AddSubgroup G} (hM : IsCoatom M) (hK : ¬K ≤ M) (j : G ⧸ M) :
    ∃ k ∈ K, (QuotientAddGroup.mk k : G ⧸ M) = j := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective j
  have hg : g ∈ K ⊔ M := by
    rw [sup_eq_top_of_not_le hM hK]; exact AddSubgroup.mem_top g
  obtain ⟨k, hk, m, hm, rfl⟩ := (AddSubgroup.mem_sup).mp hg
  refine ⟨k, hk, ?_⟩
  have hm0 : (QuotientAddGroup.mk m : G ⧸ M) = 0 := (QuotientAddGroup.eq_zero_iff m).mpr hm
  rw [QuotientAddGroup.mk_add, hm0, add_zero]

namespace ExactCosetCover

variable {ι : Type*} (P : ExactCosetCover G ι) (M : AddSubgroup G)

/-- The part at index `i` meets `M`. -/
def Meets (i : ι) : Prop := ∃ g ∈ M, g - P.base i ∈ P.sub i

/-- A B-part (`sub i ⊄ M`) meets `M` (indeed every `M`-coset), `M` a coatom. -/
theorem meets_of_not_le (hM : IsCoatom M) {i : ι} (h : ¬P.sub i ≤ M) : P.Meets M i := by
  obtain ⟨k, hk, hkj⟩ := exists_mk_eq hM h (-(QuotientAddGroup.mk (P.base i)))
  refine ⟨P.base i + k, ?_, by simp [hk]⟩
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_add, hkj, add_neg_cancel]

/-- An A-part (`sub i ≤ M`) meets `M` iff its base point lies in `M`. -/
theorem meets_iff_base_mem {i : ι} (h : P.sub i ≤ M) : P.Meets M i ↔ P.base i ∈ M := by
  constructor
  · rintro ⟨g, hgM, hgs⟩
    have h1 : g - P.base i ∈ M := h hgs
    have h2 := sub_mem hgM h1
    simpa using h2
  · intro hb
    exact ⟨P.base i, hb, by rw [sub_self]; exact (P.sub i).zero_mem⟩

/-- Chosen base point in `M` for a part meeting `M`. -/
noncomputable def restrictBase (i : {i : ι // P.Meets M i}) : M :=
  ⟨i.2.choose, i.2.choose_spec.1⟩

theorem restrictBase_spec (i : {i : ι // P.Meets M i}) :
    (P.restrictBase M i : G) - P.base i.1 ∈ P.sub i.1 :=
  i.2.choose_spec.2

/-- Membership transfer: a point of `M` lies in the restricted part iff it lies
in the ambient part. -/
theorem restrict_mem_iff (i : {i : ι // P.Meets M i}) (m : M) :
    m - P.restrictBase M i ∈ (P.sub i.1).addSubgroupOf M ↔
      (m : G) - P.base i.1 ∈ P.sub i.1 := by
  rw [AddSubgroup.mem_addSubgroupOf]
  have hcoe : ((m - P.restrictBase M i : M) : G) = (m : G) - (P.restrictBase M i : G) := rfl
  rw [hcoe]
  constructor
  · intro h
    have h2 := add_mem h (P.restrictBase_spec M i)
    rwa [sub_add_sub_cancel] at h2
  · intro h
    have h2 := sub_mem h (P.restrictBase_spec M i)
    rwa [sub_sub_sub_cancel_right] at h2

/-- **Lemma 3.1 (restriction).** The parts meeting `M`, intersected with `M`,
form an exact coset cover of `M ∖ {0}`. -/
noncomputable def restrict : ExactCosetCover M {i : ι // P.Meets M i} where
  base := P.restrictBase M
  sub i := (P.sub i.1).addSubgroupOf M
  disj := by
    rintro i j hij m ⟨hi, hj⟩
    refine P.disj i.1 j.1 (fun h => hij (Subtype.ext h)) (m : G)
      ⟨(P.restrict_mem_iff M i m).mp hi, (P.restrict_mem_iff M j m).mp hj⟩
  covers := by
    intro m
    constructor
    · intro hm
      have hm' : (m : G) ≠ 0 := fun h => hm (by ext; simpa using h)
      obtain ⟨i, hi⟩ := (P.covers (m : G)).mp hm'
      exact ⟨⟨i, ⟨(m : G), m.2, hi⟩⟩, (P.restrict_mem_iff M ⟨i, _⟩ m).mpr hi⟩
    · rintro ⟨i, hi⟩
      have h1 := (P.restrict_mem_iff M i m).mp hi
      have h2 := P.ne_zero_of_mem h1
      intro h
      exact h2 (by rw [h]; rfl)

variable [Fintype ι]

noncomputable instance : Fintype {i : ι // P.Meets M i} := Subtype.fintype _

end ExactCosetCover

end CosetCover

-- ======================= inlined: Mass.lean =======================
/-
Hunt3 / CosetCover / Mass.lean — Lemma 3.2 (mass identity / hole deficit),
run 3 wave 2 (leaf 107).

For a coatom `M ≤ G` and each class `j : G ⧸ M`, let `t_j` be the total mass
(sum of part sizes) of the A-parts (`sub i ≤ M`) sitting in the `M`-coset `j`.
Then `t_j = t_0 + 1` for every `j ≠ 0`: the nonzero cosets are heavier by
exactly the hole (STATE.md §0 Lemma 3.2; source 70 §3, re-proved 104b §S1).

Cosets are indexed by `G ⧸ M` throughout; no isomorphism to `ZMod p` is ever
chosen, and primality of the index is never used — only the coatom property.
-/

namespace CosetCover

attribute [local instance 10] Classical.propDecidable

open Finset

variable {G : Type*} [AddCommGroup G]

noncomputable instance (M : AddSubgroup G) [Fintype G] : Fintype (G ⧸ M) :=
  Fintype.ofFinite _

/-- The `M`-coset with class `j`, as a finset of `G`. -/
noncomputable def cosetFinset (M : AddSubgroup G) [Fintype G] (j : G ⧸ M) : Finset G :=
  univ.filter fun g => (QuotientAddGroup.mk g : G ⧸ M) = j

/-- The order of a subgroup, as the cardinality of its carrier finset. -/
noncomputable def subCard [Fintype G] (K : AddSubgroup G) : ℕ :=
  (univ.filter fun g => g ∈ K).card

theorem mem_cosetFinset {M : AddSubgroup G} [Fintype G] {j : G ⧸ M} {g : G} :
    g ∈ cosetFinset M j ↔ (QuotientAddGroup.mk g : G ⧸ M) = j := by
  simp [cosetFinset]

/-- All `M`-cosets have the same size. -/
theorem card_cosetFinset (M : AddSubgroup G) [Fintype G] (j : G ⧸ M) :
    (cosetFinset M j).card = (cosetFinset M 0).card := by
  obtain ⟨g₀, hg₀⟩ := QuotientAddGroup.mk_surjective j
  refine Finset.card_nbij' (fun g => g - g₀) (fun g => g + g₀) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, mem_cosetFinset] at hg ⊢
    rw [QuotientAddGroup.mk_sub, hg₀, hg, sub_self]
  · intro g hg
    simp only [Finset.mem_coe, mem_cosetFinset] at hg ⊢
    rw [QuotientAddGroup.mk_add, hg₀, hg, zero_add]
  · intro g _; simp
  · intro g _; simp

namespace ExactCosetCover

variable {ι : Type*} (P : ExactCosetCover G ι) (M : AddSubgroup G)

/-- The class in `G ⧸ M` of the part at index `i` (its "digit"). -/
def digit (i : ι) : G ⧸ M := QuotientAddGroup.mk (P.base i)

section FintypeG

variable [Fintype G]

/-- Every point of an A-part (`sub i ≤ M`) has the digit of the part. -/
theorem mk_eq_digit_of_mem {i : ι} (hle : P.sub i ≤ M) {g : G}
    (hg : g ∈ P.partFinset i) : (QuotientAddGroup.mk g : G ⧸ M) = P.digit M i := by
  have h1 : g - P.base i ∈ M := hle (P.mem_partFinset.mp hg)
  have h2 : (QuotientAddGroup.mk (g - P.base i) : G ⧸ M) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr h1
  rw [QuotientAddGroup.mk_sub] at h2
  rw [digit, ← sub_eq_zero]
  exact h2

/-- A-part trace: the whole part, if the digit matches. -/
theorem A_trace_eq {i : ι} (hle : P.sub i ≤ M) {j : G ⧸ M} (hd : P.digit M i = j) :
    P.partFinset i ∩ cosetFinset M j = P.partFinset i := by
  refine Finset.inter_eq_left.mpr fun g hg => ?_
  rw [mem_cosetFinset, P.mk_eq_digit_of_mem M hle hg, hd]

/-- A-part trace: empty, if the digit differs. -/
theorem A_trace_empty {i : ι} (hle : P.sub i ≤ M) {j : G ⧸ M} (hd : P.digit M i ≠ j) :
    P.partFinset i ∩ cosetFinset M j = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun g hg => ?_
  rw [Finset.mem_inter, mem_cosetFinset] at hg
  exact hd ((P.mk_eq_digit_of_mem M hle hg.1).symm.trans hg.2)

/-- B-part traces have the same size in every `M`-coset (`M` a coatom). -/
theorem B_trace_card (hM : IsCoatom M) {i : ι} (h : ¬P.sub i ≤ M) (j : G ⧸ M) :
    (P.partFinset i ∩ cosetFinset M j).card = (P.partFinset i ∩ cosetFinset M 0).card := by
  obtain ⟨k, hk, hkj⟩ := exists_mk_eq hM h j
  refine Finset.card_nbij' (fun g => g - k) (fun g => g + k) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_inter, P.mem_partFinset, mem_cosetFinset] at hg ⊢
    obtain ⟨hg1, hg2⟩ := hg
    constructor
    · rw [sub_right_comm]
      exact sub_mem hg1 hk
    · rw [QuotientAddGroup.mk_sub, hg2, hkj, sub_self]
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_inter, P.mem_partFinset, mem_cosetFinset] at hg ⊢
    obtain ⟨hg1, hg2⟩ := hg
    constructor
    · rw [add_sub_right_comm]
      exact add_mem hg1 hk
    · rw [QuotientAddGroup.mk_add, hg2, hkj, zero_add]
  · intro g _; simp
  · intro g _; simp

/-- Each `M`-coset is partitioned by the part traces, plus the hole in coset 0. -/
theorem coset_decomp (j : G ⧸ M) [Fintype ι] :
    (cosetFinset M j).card =
      (if j = 0 then 1 else 0) + ∑ i : ι, (P.partFinset i ∩ cosetFinset M j).card := by
  have hdisj : ∀ x ∈ (univ : Finset ι), ∀ y ∈ (univ : Finset ι), x ≠ y →
      Disjoint (P.partFinset x ∩ cosetFinset M j) (P.partFinset y ∩ cosetFinset M j) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro g hgx hgy
    rw [Finset.mem_inter, P.mem_partFinset] at hgx hgy
    exact P.disj x y hxy g ⟨hgx.1, hgy.1⟩
  have herase : (cosetFinset M j).erase 0 =
      univ.biUnion fun i => P.partFinset i ∩ cosetFinset M j := by
    ext g
    rw [Finset.mem_erase, Finset.mem_biUnion]
    constructor
    · rintro ⟨hg0, hgj⟩
      obtain ⟨i, hi⟩ := (P.covers g).mp hg0
      exact ⟨i, mem_univ i, Finset.mem_inter.mpr ⟨P.mem_partFinset.mpr hi, hgj⟩⟩
    · rintro ⟨i, -, hgi⟩
      rw [Finset.mem_inter, P.mem_partFinset] at hgi
      exact ⟨P.ne_zero_of_mem hgi.1, hgi.2⟩
  have hcard : ((cosetFinset M j).erase 0).card =
      ∑ i : ι, (P.partFinset i ∩ cosetFinset M j).card := by
    rw [herase, Finset.card_biUnion hdisj]
  by_cases hj : j = 0
  · subst hj
    have h0 : (0 : G) ∈ cosetFinset M 0 := by
      rw [mem_cosetFinset, QuotientAddGroup.mk_zero]
    rw [if_pos rfl, ← hcard, ← Finset.card_erase_add_one h0]
    omega
  · have h0 : (0 : G) ∉ cosetFinset M j := by
      rw [mem_cosetFinset, QuotientAddGroup.mk_zero]
      exact fun h => hj h.symm
    rw [if_neg hj, ← hcard, Finset.erase_eq_of_notMem h0, zero_add]

end FintypeG

section Mass

variable [Fintype G] [Fintype ι]

/-- `t_j`: total mass of the A-parts in the `M`-coset `j`. -/
noncomputable def tMass (j : G ⧸ M) : ℕ :=
  ∑ i ∈ univ.filter fun i => P.sub i ≤ M ∧ P.digit M i = j, (P.partFinset i).card

/-- The A-part traces in coset `j` sum to `t_j`. -/
theorem sum_A_traces (j : G ⧸ M) :
    ∑ i ∈ univ.filter (fun i => P.sub i ≤ M), (P.partFinset i ∩ cosetFinset M j).card
      = P.tMass M j := by
  have h1 : ∀ i ∈ univ.filter (fun i => P.sub i ≤ M),
      (P.partFinset i ∩ cosetFinset M j).card =
        if P.digit M i = j then (P.partFinset i).card else 0 := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_cases hd : P.digit M i = j
    · rw [if_pos hd, P.A_trace_eq M hi.2 hd]
    · rw [if_neg hd, P.A_trace_empty M hi.2 hd, Finset.card_empty]
  have hst : (univ.filter (fun i => P.sub i ≤ M)).filter (fun i => P.digit M i = j)
      = univ.filter fun i => P.sub i ≤ M ∧ P.digit M i = j := by
    ext i; simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, hst]
  rfl

/-- **Lemma 3.2 (mass identity / hole deficit).** For a coatom `M` and any
`j ≠ 0`, the A-mass in coset `j` exceeds the A-mass in `M` by exactly one. -/
theorem massIdentity (hM : IsCoatom M) {j : G ⧸ M} (hj : j ≠ 0) :
    P.tMass M j = P.tMass M 0 + 1 := by
  have key : ∀ j' : G ⧸ M,
      (if j' = 0 then 1 else 0) + (P.tMass M j' +
        ∑ i ∈ univ.filter (fun i => ¬P.sub i ≤ M),
          (P.partFinset i ∩ cosetFinset M 0).card) = (cosetFinset M 0).card := by
    intro j'
    have hB : ∀ i ∈ univ.filter (fun i => ¬P.sub i ≤ M),
        (P.partFinset i ∩ cosetFinset M j').card =
          (P.partFinset i ∩ cosetFinset M 0).card := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact P.B_trace_card M hM hi.2 j'
    rw [← card_cosetFinset M j', P.coset_decomp M j',
      ← Finset.sum_filter_add_sum_filter_not univ (fun i => P.sub i ≤ M)
        (fun i => (P.partFinset i ∩ cosetFinset M j').card),
      P.sum_A_traces M j', Finset.sum_congr rfl hB]
  have h1 := key j
  have h2 := key 0
  rw [if_neg hj] at h1
  rw [if_pos rfl] at h2
  omega

/-- `c_{K,j}`: the number of parts that are cosets of `K` with digit `j`. -/
noncomputable def cIn [DecidableEq (AddSubgroup G)] (K : AddSubgroup G) (j : G ⧸ M) : ℕ :=
  ((P.fiber K).filter fun i => P.digit M i = j).card

section UsedSplit

variable [DecidableEq (AddSubgroup G)]

/-- The used subgroups contained in `M` ("A"). -/
noncomputable def subA : Finset (AddSubgroup G) := P.used.filter fun K => K ≤ M

/-- The used subgroups not contained in `M` ("B"). -/
noncomputable def subB : Finset (AddSubgroup G) := P.used.filter fun K => ¬K ≤ M

omit [Fintype ι] [DecidableEq (AddSubgroup G)] in
theorem partFinset_card (i : ι) : (P.partFinset i).card = subCard (P.sub i) := by
  rw [P.card_partFinset i]
  rfl

/-- `t_j` in per-subgroup form: `t_j = Σ_{K ∈ A} c_{K,j} · |K|`. -/
theorem tMass_eq (j : G ⧸ M) :
    P.tMass M j = ∑ K ∈ P.subA M, P.cIn M K j * subCard K := by
  have hmaps : ∀ i ∈ univ.filter (fun i => P.sub i ≤ M ∧ P.digit M i = j),
      P.sub i ∈ P.subA M := by
    intro i hi
    rw [Finset.mem_filter] at hi
    simp only [subA, Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem P.sub (mem_univ i), hi.2.1⟩
  have h0 : P.tMass M j
      = ∑ i ∈ univ.filter (fun i => P.sub i ≤ M ∧ P.digit M i = j), subCard (P.sub i) :=
    Finset.sum_congr rfl fun i _ => P.partFinset_card i
  have h1 : ∑ i ∈ univ.filter (fun i => P.sub i ≤ M ∧ P.digit M i = j), subCard (P.sub i)
      = ∑ K ∈ P.subA M, ∑ i ∈ (univ.filter
          (fun i => P.sub i ≤ M ∧ P.digit M i = j)).filter (fun i => P.sub i = K),
            subCard (P.sub i) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h2 : ∀ K ∈ P.subA M,
      ∑ i ∈ (univ.filter (fun i => P.sub i ≤ M ∧ P.digit M i = j)).filter
        (fun i => P.sub i = K), subCard (P.sub i) = P.cIn M K j * subCard K := by
    intro K hK
    simp only [subA, Finset.mem_filter] at hK
    show _ = ((P.fiber K).filter fun i => P.digit M i = j).card * subCard K
    have hset : (univ.filter (fun i => P.sub i ≤ M ∧ P.digit M i = j)).filter
        (fun i => P.sub i = K) = (P.fiber K).filter fun i => P.digit M i = j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fiber]
      constructor
      · rintro ⟨⟨-, hd⟩, hs⟩; exact ⟨hs, hd⟩
      · rintro ⟨hs, hd⟩; exact ⟨⟨hs ▸ hK.2, hd⟩, hs⟩
    have hval : ∀ i ∈ (univ.filter (fun i => P.sub i ≤ M ∧ P.digit M i = j)).filter
        (fun i => P.sub i = K), subCard (P.sub i) = subCard K := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hset, smul_eq_mul]
  rw [h0, h1]
  exact Finset.sum_congr rfl h2

/-- The digit decomposition of a multiplicity: `c_K = Σ_j c_{K,j}`. -/
theorem mult_eq_sum_cIn (K : AddSubgroup G) :
    P.mult K = ∑ j : G ⧸ M, P.cIn M K j :=
  Finset.card_eq_sum_card_fiberwise fun i _ => mem_univ (P.digit M i)

end UsedSplit

end Mass

end ExactCosetCover

end CosetCover

-- ======================= inlined: LemmaD.lean =======================
/-
Hunt3 / CosetCover / LemmaD.lean — Lemma D (per-coset domination),
run 3 wave 2 (leaf 107). Source: 104 §Result 2, hostile-checked 104b §S2.

For every coatom `M` and every nonzero class `j : G ⧸ M`:
  `S_j := Σ_{K ∈ A} c_{K,j} / (c_{K,0} + 1) ≥ 1`.

Proof: if `S_j < 1` then every term is `< 1`; numerator and denominator are
indexed by the SAME `K`, so `c_{K,j} ≤ c_{K,0}` by integrality, for every
`K ∈ A`; multiplying by `|K|` and summing gives `t_j ≤ t_0`, contradicting the
hole deficit `t_j = t_0 + 1` (Lemma 3.2).
-/

namespace CosetCover

attribute [local instance 10] Classical.propDecidable

open Finset

namespace ExactCosetCover

variable {G : Type*} [AddCommGroup G] {ι : Type*}
variable (P : ExactCosetCover G ι) (M : AddSubgroup G)
variable [Fintype G] [Fintype ι] [DecidableEq (AddSubgroup G)]

/-- **Lemma D (per-coset domination).** For a coatom `M` and any `j ≠ 0`,
`Σ_{K ∈ A} c_{K,j} / (c_{K,0} + 1) ≥ 1`. -/
theorem lemmaD (hM : IsCoatom M) {j : G ⧸ M} (hj : j ≠ 0) :
    (1 : ℚ) ≤ ∑ K ∈ P.subA M, (P.cIn M K j : ℚ) / (P.cIn M K 0 + 1) := by
  by_contra hlt
  rw [not_le] at hlt
  have hterm : ∀ K ∈ P.subA M, P.cIn M K j ≤ P.cIn M K 0 := by
    intro K hK
    have hone : (P.cIn M K j : ℚ) / (P.cIn M K 0 + 1) < 1 :=
      lt_of_le_of_lt
        (Finset.single_le_sum (f := fun K => (P.cIn M K j : ℚ) / (P.cIn M K 0 + 1))
          (fun K _ => by positivity) hK) hlt
    have hcast : (P.cIn M K j : ℚ) < (P.cIn M K 0 : ℚ) + 1 :=
      (div_lt_one (by positivity)).mp hone
    have : P.cIn M K j < P.cIn M K 0 + 1 := by exact_mod_cast hcast
    omega
  have hle : P.tMass M j ≤ P.tMass M 0 := by
    rw [P.tMass_eq M j, P.tMass_eq M 0]
    exact Finset.sum_le_sum fun K hK => Nat.mul_le_mul_right _ (hterm K hK)
  have := P.massIdentity M hM hj
  omega

end ExactCosetCover

end CosetCover

-- ======================= inlined: Local.lean =======================
/-
Hunt3 / CosetCover / Local.lean — the local inequality (*) at EVERY coatom `M`,
run 3 wave 2 (leaf 107). Source: 104 §Result 2 Theorem, hostile-checked 104b §S3.

  (*)  `index(M) · Π_{K ∈ A} (c_{K,0} + 1) ≤ Π_{K ∈ A} (c_K + 1)`.

Proof: `(c_K+1)/(c_{K,0}+1) = 1 + x_K` with
`x_K = Σ_{j ≠ 0} c_{K,j}/(c_{K,0}+1) ≥ 0` (digit decomposition is exact),
Weierstrass `Π(1+x_K) ≥ 1 + Σ x_K`, and `Σ_K x_K = Σ_{j≠0} S_j ≥ index − 1`
by Lemma D. Only the coatom property is used; the index need not be prime.
-/

namespace CosetCover

attribute [local instance 10] Classical.propDecidable

open Finset

/-- Weierstrass product inequality, ℕ version: `1 + Σ f ≤ Π (f + 1)`. -/
theorem one_add_sum_le_prod_add_one {α : Type*} (s : Finset α) (f : α → ℕ) :
    1 + ∑ a ∈ s, f a ≤ ∏ a ∈ s, (f a + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    calc 1 + (f a + ∑ b ∈ s, f b)
        ≤ 1 + (f a + ∑ b ∈ s, f b) + f a * ∑ b ∈ s, f b := Nat.le_add_right _ _
      _ = (f a + 1) * (1 + ∑ b ∈ s, f b) := by ring
      _ ≤ (f a + 1) * ∏ b ∈ s, (f b + 1) := Nat.mul_le_mul_left _ ih

/-- Weierstrass product inequality, ℚ version: `1 + Σ x ≤ Π (1 + x)` for
nonnegative `x`. -/
theorem one_add_sum_le_prod_one_add {α : Type*} (s : Finset α) (x : α → ℚ)
    (hx : ∀ a ∈ s, 0 ≤ x a) : 1 + ∑ a ∈ s, x a ≤ ∏ a ∈ s, (1 + x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hs : ∀ b ∈ s, 0 ≤ x b := fun b hb => hx b (Finset.mem_insert_of_mem hb)
    have h1 : 1 + ∑ b ∈ s, x b ≤ ∏ b ∈ s, (1 + x b) := ih hs
    have h2 : 0 ≤ ∑ b ∈ s, x b := Finset.sum_nonneg hs
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℚ) ≤ 1 + x a)]

namespace ExactCosetCover

variable {G : Type*} [AddCommGroup G] {ι : Type*}
variable (P : ExactCosetCover G ι) (M : AddSubgroup G)
variable [Fintype G] [Fintype ι] [DecidableEq (AddSubgroup G)]

/-- **The local inequality (*) at every coatom.** For every coatom `M`,
`index(M) · Π_{K ∈ A} (c_{K,0} + 1) ≤ Π_{K ∈ A} (c_K + 1)`. -/
theorem star (hM : IsCoatom M) :
    M.index * ∏ K ∈ P.subA M, (P.cIn M K 0 + 1) ≤ ∏ K ∈ P.subA M, (P.mult K + 1) := by
  have hd : ∀ K : AddSubgroup G, (0 : ℚ) < (P.cIn M K 0 : ℚ) + 1 := fun K => by positivity
  set x : AddSubgroup G → ℚ := fun K =>
    ∑ j ∈ (univ : Finset (G ⧸ M)).erase 0, (P.cIn M K j : ℚ) / ((P.cIn M K 0 : ℚ) + 1)
    with hxdef
  have hxnn : ∀ K ∈ P.subA M, 0 ≤ x K := fun K _ =>
    Finset.sum_nonneg fun j _ => by positivity
  -- the exact ratio identity (c_K + 1) = (c_{K,0} + 1) · (1 + x_K)
  have hratio : ∀ K ∈ P.subA M,
      ((P.mult K : ℚ) + 1) = ((P.cIn M K 0 : ℚ) + 1) * (1 + x K) := by
    intro K _
    have h1 : P.mult K = P.cIn M K 0 + ∑ j ∈ (univ : Finset (G ⧸ M)).erase 0, P.cIn M K j := by
      rw [P.mult_eq_sum_cIn M K, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G ⧸ M))]
    have hsum : ∀ j ∈ (univ : Finset (G ⧸ M)).erase 0,
        ((P.cIn M K 0 : ℚ) + 1) * ((P.cIn M K j : ℚ) / ((P.cIn M K 0 : ℚ) + 1))
          = (P.cIn M K j : ℚ) := fun j _ => mul_div_cancel₀ _ (ne_of_gt (hd K))
    rw [h1]
    push_cast
    rw [mul_add, mul_one, hxdef, Finset.mul_sum, Finset.sum_congr rfl hsum]
    ring
  -- product form
  have hprod : ∏ K ∈ P.subA M, ((P.mult K : ℚ) + 1)
      = (∏ K ∈ P.subA M, ((P.cIn M K 0 : ℚ) + 1)) * ∏ K ∈ P.subA M, (1 + x K) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hratio
  -- Σ_K x_K ≥ index − 1, via Lemma D per nonzero class
  have hsx : (M.index : ℚ) - 1 ≤ ∑ K ∈ P.subA M, x K := by
    have hswap : ∑ K ∈ P.subA M, x K = ∑ j ∈ (univ : Finset (G ⧸ M)).erase 0,
        ∑ K ∈ P.subA M, (P.cIn M K j : ℚ) / ((P.cIn M K 0 : ℚ) + 1) := by
      rw [hxdef]
      exact Finset.sum_comm
    have hbound : ∀ j ∈ (univ : Finset (G ⧸ M)).erase 0,
        (1 : ℚ) ≤ ∑ K ∈ P.subA M, (P.cIn M K j : ℚ) / ((P.cIn M K 0 : ℚ) + 1) := by
      intro j hj
      exact P.lemmaD M hM (Finset.mem_erase.mp hj).1
    have hcardpos : 1 ≤ Fintype.card (G ⧸ M) := Fintype.card_pos
    have hindex : M.index = Fintype.card (G ⧸ M) := by
      rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
    calc (M.index : ℚ) - 1
        = (((univ : Finset (G ⧸ M)).erase 0).card : ℚ) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hindex]
          rw [Nat.cast_sub hcardpos]
          push_cast
          ring
      _ = ∑ _j ∈ (univ : Finset (G ⧸ M)).erase 0, (1 : ℚ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := by rw [hswap]; exact Finset.sum_le_sum hbound
  -- assemble in ℚ
  have hfinal : (M.index : ℚ) * ∏ K ∈ P.subA M, ((P.cIn M K 0 : ℚ) + 1)
      ≤ ∏ K ∈ P.subA M, ((P.mult K : ℚ) + 1) := by
    have hW : 1 + ∑ K ∈ P.subA M, x K ≤ ∏ K ∈ P.subA M, (1 + x K) :=
      one_add_sum_le_prod_one_add _ _ hxnn
    have hidx : (M.index : ℚ) ≤ ∏ K ∈ P.subA M, (1 + x K) := by linarith
    have hpd : (0 : ℚ) ≤ ∏ K ∈ P.subA M, ((P.cIn M K 0 : ℚ) + 1) :=
      le_of_lt (Finset.prod_pos fun K _ => hd K)
    calc (M.index : ℚ) * ∏ K ∈ P.subA M, ((P.cIn M K 0 : ℚ) + 1)
        = (∏ K ∈ P.subA M, ((P.cIn M K 0 : ℚ) + 1)) * (M.index : ℚ) := by ring
      _ ≤ (∏ K ∈ P.subA M, ((P.cIn M K 0 : ℚ) + 1)) * ∏ K ∈ P.subA M, (1 + x K) :=
          mul_le_mul_of_nonneg_left hidx hpd
      _ = ∏ K ∈ P.subA M, ((P.mult K : ℚ) + 1) := hprod.symm
  exact_mod_cast hfinal

end ExactCosetCover

end CosetCover

-- ======================= inlined: Induction.lean =======================
/-
Hunt3 / CosetCover / Induction.lean — LEMMA C, run 3 wave 2 (leaf 107).
Source: P11 = 104 §Result 2 (Corollary), hostile-checked 104b §S4.

**Lemma C.** For every finite abelian group `G` and every partition of `G`
into cosets with singleton hole `{0}`, `|G| ≤ Π_K (c_K + 1)` over the distinct
used subgroups `K` with multiplicities `c_K`.

Proof by strong induction on `|G|`: pick any coatom `M`; restrict (Lemma 3.1,
`Restrict.lean`); apply the inductive hypothesis to the restricted cover of
`M`; the padding inequality bounds the restricted product by
`Π_A (c_{K,0}+1) · Π_B (c_K+1)`; and (*) at `M` (`Local.lean`, from Lemma D and
the mass identity) trades `index(M) · Π_A (c_{K,0}+1)` for `Π_A (c_K+1)`.
-/

namespace CosetCover

attribute [local instance 10] Classical.propDecidable

open Finset

universe u v

/-- Counting a predicate on a subtype as a conjunction downstairs. -/
theorem card_subtype_filter {ι : Type*} [Fintype ι] (p q : ι → Prop)
    [Fintype {i : ι // p i}] [DecidablePred fun i : {i : ι // p i} => q i.1]
    [DecidablePred fun i => p i ∧ q i] :
    ((univ : Finset {i : ι // p i}).filter fun i => q i.1).card
      = (univ.filter fun i => p i ∧ q i).card := by
  refine Finset.card_nbij (fun a => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨mem_univ _, a.2, ha.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    exact ⟨⟨a, ha.2.1⟩, by simp [ha.2.2], rfl⟩

/-- Every nontrivial finite abelian group has a maximal proper subgroup. -/
theorem exists_isCoatom (G : Type*) [AddCommGroup G] [Finite G] [Nontrivial G] :
    ∃ M : AddSubgroup G, IsCoatom M := by
  have hbt : (⊥ : AddSubgroup G) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : G)
    intro h
    have hx0 : x ∈ (⊥ : AddSubgroup G) := by rw [h]; exact AddSubgroup.mem_top x
    exact hx (AddSubgroup.mem_bot.mp hx0)
  have hfin : Finite (AddSubgroup G) :=
    Finite.of_injective (fun H => (H : Set G)) SetLike.coe_injective
  rcases eq_top_or_exists_le_coatom (⊥ : AddSubgroup G) with h | ⟨M, hM, -⟩
  · exact absurd h hbt
  · exact ⟨M, hM⟩

namespace ExactCosetCover

variable {G : Type u} [AddCommGroup G] {ι : Type v}
variable (P : ExactCosetCover G ι) (M : AddSubgroup G)
variable [Fintype G] [Fintype ι] [DecidableEq (AddSubgroup G)]

omit [Fintype G] in
/-- The multiplicity of a restricted used subgroup `L ≤ M` in per-ambient form:
digit-0 counts from the A-side, full multiplicities from the B-side. -/
theorem restrict_mult_eq (hM : IsCoatom M) (L : AddSubgroup M) :
    (P.restrict M).mult L
      = (∑ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), P.cIn M K 0)
        + ∑ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), P.mult K := by
  have hmaps : ∀ i' ∈ (univ : Finset {i // P.Meets M i}).filter
      (fun i' => (P.sub i'.1).addSubgroupOf M = L),
      P.sub i'.1 ∈ P.used.filter (fun K => K.addSubgroupOf M = L) := by
    intro i' hi'
    rw [Finset.mem_filter] at hi' ⊢
    exact ⟨Finset.mem_image_of_mem _ (mem_univ _), hi'.2⟩
  have h2 : ∀ K ∈ P.used.filter (fun K => K.addSubgroupOf M = L),
      (((univ : Finset {i // P.Meets M i}).filter
          (fun i' => (P.sub i'.1).addSubgroupOf M = L)).filter
        (fun i' => P.sub i'.1 = K)).card
      = ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card := by
    intro K hK
    rw [Finset.mem_filter] at hK
    congr 1
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact hK.2, h⟩
  have h1 : (P.restrict M).mult L = ∑ K ∈ P.used.filter (fun K => K.addSubgroupOf M = L),
      ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card :=
    calc (P.restrict M).mult L
        = ((univ : Finset {i // P.Meets M i}).filter
            (fun i' => (P.sub i'.1).addSubgroupOf M = L)).card := rfl
      _ = ∑ K ∈ P.used.filter (fun K => K.addSubgroupOf M = L),
            (((univ : Finset {i // P.Meets M i}).filter
                (fun i' => (P.sub i'.1).addSubgroupOf M = L)).filter
              (fun i' => P.sub i'.1 = K)).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ = _ := Finset.sum_congr rfl h2
  have hA : ∀ K, K ≤ M →
      ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card
        = P.cIn M K 0 := by
    intro K hKM
    rw [card_subtype_filter (fun i => P.Meets M i) (fun i => P.sub i = K)]
    have hset : (univ.filter fun i => P.Meets M i ∧ P.sub i = K)
        = (P.fiber K).filter (fun i => P.digit M i = 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fiber]
      constructor
      · rintro ⟨hm, hs⟩
        refine ⟨hs, ?_⟩
        have hbase : P.base i ∈ M := (P.meets_iff_base_mem M (hs.le.trans hKM)).mp hm
        exact (QuotientAddGroup.eq_zero_iff _).mpr hbase
      · rintro ⟨hs, hd⟩
        refine ⟨?_, hs⟩
        have hbase : P.base i ∈ M := (QuotientAddGroup.eq_zero_iff _).mp hd
        exact (P.meets_iff_base_mem M (hs.le.trans hKM)).mpr hbase
    rw [hset]
    rfl
  have hB : ∀ K, ¬K ≤ M →
      ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card
        = P.mult K := by
    intro K hKM
    rw [card_subtype_filter (fun i => P.Meets M i) (fun i => P.sub i = K)]
    have hset : (univ.filter fun i => P.Meets M i ∧ P.sub i = K) = P.fiber K := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fiber]
      constructor
      · rintro ⟨-, hs⟩; exact hs
      · intro hs
        exact ⟨P.meets_of_not_le M hM (fun hle => hKM (hs ▸ hle)), hs⟩
    rw [hset]
    rfl
  have hAL : (P.used.filter (fun K => K.addSubgroupOf M = L)).filter (fun K => K ≤ M)
      = (P.subA M).filter (fun K => K.addSubgroupOf M = L) := by
    ext K
    simp only [Finset.mem_filter, subA]
    tauto
  have hBL : (P.used.filter (fun K => K.addSubgroupOf M = L)).filter (fun K => ¬K ≤ M)
      = (P.subB M).filter (fun K => K.addSubgroupOf M = L) := by
    ext K
    simp only [Finset.mem_filter, subB]
    tauto
  calc (P.restrict M).mult L
      = ∑ K ∈ P.used.filter (fun K => K.addSubgroupOf M = L),
          ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card := h1
    _ = (∑ K ∈ (P.used.filter (fun K => K.addSubgroupOf M = L)).filter (fun K => K ≤ M),
          ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card)
        + ∑ K ∈ (P.used.filter (fun K => K.addSubgroupOf M = L)).filter (fun K => ¬K ≤ M),
          ((univ : Finset {i // P.Meets M i}).filter (fun i' => P.sub i'.1 = K)).card :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ = (∑ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), P.cIn M K 0)
        + ∑ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), P.mult K := by
        refine congrArg₂ (· + ·) ?_ ?_
        · refine Finset.sum_congr hAL fun K hK => ?_
          rw [Finset.mem_filter] at hK
          have hKM : K ≤ M := by
            have := hK.1
            simp only [subA, Finset.mem_filter] at this
            exact this.2
          exact hA K hKM
        · refine Finset.sum_congr hBL fun K hK => ?_
          rw [Finset.mem_filter] at hK
          have hKM : ¬K ≤ M := by
            have := hK.1
            simp only [subB, Finset.mem_filter] at this
            exact this.2
          exact hB K hKM

omit [Fintype G] in
/-- **The padding inequality**: the restricted product is at most
`Π_A (c_{K,0}+1) · Π_B (c_K+1)`. -/
theorem padding (hM : IsCoatom M) :
    ∏ L ∈ (P.restrict M).used, ((P.restrict M).mult L + 1)
      ≤ (∏ K ∈ P.subA M, (P.cIn M K 0 + 1)) * ∏ K ∈ P.subB M, (P.mult K + 1) := by
  have hperL : ∀ L ∈ (P.restrict M).used,
      (P.restrict M).mult L + 1 ≤
        (∏ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1))
          * ∏ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), (P.mult K + 1) := by
    intro L _
    rw [P.restrict_mult_eq M hM L]
    have hA : 1 + ∑ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), P.cIn M K 0
        ≤ ∏ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1) :=
      one_add_sum_le_prod_add_one _ _
    have hB : 1 + ∑ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), P.mult K
        ≤ ∏ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), (P.mult K + 1) :=
      one_add_sum_le_prod_add_one _ _
    set a := ∑ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), P.cIn M K 0 with ha
    set b := ∑ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), P.mult K with hb
    calc a + b + 1 ≤ a + b + 1 + a * b := Nat.le_add_right _ _
      _ = (1 + a) * (1 + b) := by ring
      _ ≤ _ := Nat.mul_le_mul hA hB
  have hAgg : ∏ L ∈ (P.restrict M).used,
      ∏ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1)
        ≤ ∏ K ∈ P.subA M, (P.cIn M K 0 + 1) := by
    have hindexeq : ∀ L ∈ (P.restrict M).used,
        (P.subA M).filter (fun K => K.addSubgroupOf M = L)
          = ((P.subA M).filter
              (fun K => K.addSubgroupOf M ∈ (P.restrict M).used)).filter
            (fun K => K.addSubgroupOf M = L) := by
      intro L hL
      ext K
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hK1, hK2⟩; exact ⟨⟨hK1, hK2 ▸ hL⟩, hK2⟩
      · rintro ⟨⟨hK1, -⟩, hK2⟩; exact ⟨hK1, hK2⟩
    calc ∏ L ∈ (P.restrict M).used,
          ∏ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1)
        = ∏ L ∈ (P.restrict M).used,
            ∏ K ∈ ((P.subA M).filter
                (fun K => K.addSubgroupOf M ∈ (P.restrict M).used)).filter
              (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1) :=
          Finset.prod_congr rfl fun L hL => by rw [← hindexeq L hL]
      _ = ∏ K ∈ (P.subA M).filter
            (fun K => K.addSubgroupOf M ∈ (P.restrict M).used), (P.cIn M K 0 + 1) :=
          Finset.prod_fiberwise_of_maps_to (fun K hK => (Finset.mem_filter.mp hK).2) _
      _ ≤ ∏ K ∈ P.subA M, (P.cIn M K 0 + 1) :=
          Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
            (fun K _ _ => Nat.le_add_left 1 _)
  have hBgg : ∏ L ∈ (P.restrict M).used,
      ∏ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), (P.mult K + 1)
        ≤ ∏ K ∈ P.subB M, (P.mult K + 1) := by
    have hindexeq : ∀ L ∈ (P.restrict M).used,
        (P.subB M).filter (fun K => K.addSubgroupOf M = L)
          = ((P.subB M).filter
              (fun K => K.addSubgroupOf M ∈ (P.restrict M).used)).filter
            (fun K => K.addSubgroupOf M = L) := by
      intro L hL
      ext K
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hK1, hK2⟩; exact ⟨⟨hK1, hK2 ▸ hL⟩, hK2⟩
      · rintro ⟨⟨hK1, -⟩, hK2⟩; exact ⟨hK1, hK2⟩
    calc ∏ L ∈ (P.restrict M).used,
          ∏ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), (P.mult K + 1)
        = ∏ L ∈ (P.restrict M).used,
            ∏ K ∈ ((P.subB M).filter
                (fun K => K.addSubgroupOf M ∈ (P.restrict M).used)).filter
              (fun K => K.addSubgroupOf M = L), (P.mult K + 1) :=
          Finset.prod_congr rfl fun L hL => by rw [← hindexeq L hL]
      _ = ∏ K ∈ (P.subB M).filter
            (fun K => K.addSubgroupOf M ∈ (P.restrict M).used), (P.mult K + 1) :=
          Finset.prod_fiberwise_of_maps_to (fun K hK => (Finset.mem_filter.mp hK).2) _
      _ ≤ ∏ K ∈ P.subB M, (P.mult K + 1) :=
          Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
            (fun K _ _ => Nat.le_add_left 1 _)
  calc ∏ L ∈ (P.restrict M).used, ((P.restrict M).mult L + 1)
      ≤ ∏ L ∈ (P.restrict M).used,
          ((∏ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1))
            * ∏ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), (P.mult K + 1)) :=
        Finset.prod_le_prod' hperL
    _ = (∏ L ∈ (P.restrict M).used,
          ∏ K ∈ (P.subA M).filter (fun K => K.addSubgroupOf M = L), (P.cIn M K 0 + 1))
        * ∏ L ∈ (P.restrict M).used,
          ∏ K ∈ (P.subB M).filter (fun K => K.addSubgroupOf M = L), (P.mult K + 1) :=
        Finset.prod_mul_distrib
    _ ≤ _ := Nat.mul_le_mul hAgg hBgg

end ExactCosetCover

/-- The inductive engine: Lemma C for all groups of cardinality at most `n`. -/
theorem lemmaC_of_card_le : ∀ (n : ℕ) (G : Type u) [AddCommGroup G] [Fintype G]
    [DecidableEq (AddSubgroup G)] (ι : Type v) [Fintype ι] (P : ExactCosetCover G ι),
    Fintype.card G ≤ n → Fintype.card G ≤ ∏ K ∈ P.used, (P.mult K + 1) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ ι _ P hn
    have : 0 < Fintype.card G := Fintype.card_pos
    omega
  | succ n IH =>
    intro G _ _ _ ι _ P hn
    by_cases hle : Fintype.card G ≤ n
    · exact IH G ι P hle
    by_cases htriv : Fintype.card G ≤ 1
    · have h1 : (1 : ℕ) ≤ ∏ K ∈ P.used, (P.mult K + 1) :=
        Finset.one_le_prod' fun K _ => Nat.le_add_left 1 _
      omega
    have hnt : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨M, hM⟩ := exists_isCoatom G
    have hne1 : M.index ≠ 1 := fun h => hM.1 (AddSubgroup.index_eq_one.mp h)
    have hne0 : M.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    have hix : M.index * Fintype.card M = Fintype.card G := by
      rw [← Nat.card_eq_fintype_card (α := M), ← Nat.card_eq_fintype_card (α := G)]
      exact AddSubgroup.index_mul_card M
    have hMlt : Fintype.card M < Fintype.card G := by
      have h2 : 2 ≤ M.index := by omega
      have hpos : 0 < Fintype.card M := Fintype.card_pos
      have h3 : 2 * Fintype.card M ≤ M.index * Fintype.card M :=
        Nat.mul_le_mul_right _ h2
      omega
    have hcard : Fintype.card M ≤ n := by omega
    have hIH := IH M {i : ι // P.Meets M i} (P.restrict M) hcard
    have hpad := P.padding M hM
    have hstar := P.star M hM
    calc Fintype.card G = M.index * Fintype.card M := hix.symm
      _ ≤ M.index * ∏ L ∈ (P.restrict M).used, ((P.restrict M).mult L + 1) :=
          Nat.mul_le_mul_left _ hIH
      _ ≤ M.index * ((∏ K ∈ P.subA M, (P.cIn M K 0 + 1))
            * ∏ K ∈ P.subB M, (P.mult K + 1)) :=
          Nat.mul_le_mul_left _ hpad
      _ = (M.index * ∏ K ∈ P.subA M, (P.cIn M K 0 + 1))
            * ∏ K ∈ P.subB M, (P.mult K + 1) := (mul_assoc _ _ _).symm
      _ ≤ (∏ K ∈ P.subA M, (P.mult K + 1)) * ∏ K ∈ P.subB M, (P.mult K + 1) :=
          Nat.mul_le_mul_right _ hstar
      _ = ∏ K ∈ P.used, (P.mult K + 1) := by
          simp only [ExactCosetCover.subA, ExactCosetCover.subB]
          exact Finset.prod_filter_mul_prod_filter_not _ _ _

/-- **LEMMA C** (P11, machine-checked): for every finite abelian group `G` and
every exact coset cover of `G ∖ {0}` with hole `{0}`,
`|G| ≤ Π_K (c_K + 1)` over the distinct used subgroups. -/
theorem ExactCosetCover.lemmaC_holds {G : Type u} [AddCommGroup G] [Fintype G]
    {ι : Type v} [Fintype ι] [DecidableEq (AddSubgroup G)]
    (P : ExactCosetCover G ι) : P.LemmaC :=
  lemmaC_of_card_le (Fintype.card G) G ι P le_rfl

end CosetCover


/-! ## The arithmetic ceiling: the exact optimum of the block-product functional -/

namespace Arith
open Finset

/-- `D t = 5 - t % 2`: the parity discount, `5` on evens and `4` on odds. -/
def D (t : ℕ) : ℕ := 5 - t % 2
lemma D_even {t : ℕ} (h : t % 2 = 0) : D t = 5 := by simp [D, h]
lemma D_odd  {t : ℕ} (h : t % 2 = 1) : D t = 4 := by simp [D, h]
lemma D_le (t : ℕ) : D t ≤ 5 := by simp only [D]; omega

lemma cs (u v : ℕ) : (u*v+1)^2 ≤ (u^2+1)*(v^2+1) := by
  have h : (2*u*v : ℤ) ≤ (u:ℤ)^2 + (v:ℤ)^2 := by nlinarith [sq_nonneg ((u:ℤ) - v)]
  have h' : 2*u*v ≤ u^2+v^2 := by exact_mod_cast h
  nlinarith [h']

lemma key2 : ∀ u : ℕ, (u^2+1)^2 ≤ 5^u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    match u with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | (k+3) =>
      have h := ih (k+2) (by omega)
      have hid : 5*((k+2)^2+1)^2 = ((k+3)^2+1)^2 + (4*k^4+28*k^3+74*k^2+80*k+25) := by ring
      have step : ((k+3)^2+1)^2 ≤ 5 * ((k+2)^2+1)^2 := by rw [hid]; exact Nat.le_add_right _ _
      calc ((k+3)^2+1)^2 ≤ 5 * ((k+2)^2+1)^2 := step
        _ ≤ 5 * 5^(k+2) := Nat.mul_le_mul_left 5 h
        _ = 5^(k+3) := by ring

lemma key3 : ∀ j : ℕ, 5*((2*j+1)^2+1)^2 ≤ 4*5^(2*j+1) := by
  intro j
  induction j with
  | zero => norm_num
  | succ i ih =>
    have hid : 25*((2*i+1)^2+1)^2
        = ((2*(i+1)+1)^2+1)^2 + (384*i^4+704*i^3+576*i^2+160*i) := by ring
    have step : ((2*(i+1)+1)^2+1)^2 ≤ 25 * ((2*i+1)^2+1)^2 := by
      rw [hid]; exact Nat.le_add_right _ _
    calc 5*((2*(i+1)+1)^2+1)^2 ≤ 5 * (25 * ((2*i+1)^2+1)^2) := Nat.mul_le_mul_left 5 step
      _ = 25 * (5*((2*i+1)^2+1)^2) := by ring
      _ ≤ 25 * (4*5^(2*i+1)) := Nat.mul_le_mul_left 25 ih
      _ = 4*5^(2*(i+1)+1) := by ring

lemma keyK (u a : ℕ) : (u^2+1)^2 * D a ≤ 5^u * D (u+a) := by
  rcases Nat.even_or_odd u with he | ho
  · have hu : u % 2 = 0 := Nat.even_iff.mp he
    have h : (u+a) % 2 = a % 2 := by omega
    simp only [D, h]
    exact Nat.mul_le_mul_right _ (key2 u)
  · obtain ⟨j, hj⟩ := ho
    have hu : u % 2 = 1 := by omega
    have h3 : 5*(u^2+1)^2 ≤ 4*5^u := by
      have hk := key3 j
      have e : 2*j+1 = u := by omega
      rw [e] at hk
      exact hk
    rcases Nat.even_or_odd a with hae | hao
    · have ha : a % 2 = 0 := Nat.even_iff.mp hae
      have hua : (u+a) % 2 = 1 := by omega
      rw [D_even ha, D_odd hua]
      calc (u^2+1)^2 * 5 = 5*(u^2+1)^2 := by ring
        _ ≤ 4*5^u := h3
        _ = 5^u * 4 := by ring
    · obtain ⟨i, hi⟩ := hao
      have ha : a % 2 = 1 := by omega
      have hua : (u+a) % 2 = 0 := by omega
      rw [D_odd ha, D_even hua]
      calc (u^2+1)^2 * 4 ≤ 5^u * 4 := Nat.mul_le_mul_right _ (key2 u)
        _ ≤ 5^u * 5 := Nat.mul_le_mul_left _ (by norm_num)

variable {α : Type*} [DecidableEq α]

theorem potentialF (s : Finset α) (u v : α → ℕ) :
    25 * (∏ i ∈ s, (u i * v i + 1))^4
      ≤ 5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i)) * D (∑ i ∈ s, u i) * D (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : (u x * v x+1)^4 ≤ ((u x)^2+1)^2 * ((v x)^2+1)^2 := by
      have hcs := cs (u x) (v x)
      calc (u x * v x+1)^4 = ((u x * v x+1)^2)^2 := by ring
        _ ≤ (((u x)^2+1)*((v x)^2+1))^2 := Nat.pow_le_pow_left hcs 2
        _ = ((u x)^2+1)^2 * ((v x)^2+1)^2 := by ring
    calc 25 * ((u x * v x + 1) * ∏ i ∈ s, (u i * v i + 1))^4
        = (u x * v x+1)^4 * (25 * (∏ i ∈ s, (u i * v i + 1))^4) := by ring
      _ ≤ (((u x)^2+1)^2 * ((v x)^2+1)^2)
            * (5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i)) * D (∑ i ∈ s, u i) * D (∑ i ∈ s, v i)) :=
          Nat.mul_le_mul h1 ih
      _ = 5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i))
            * (((u x)^2+1)^2 * D (∑ i ∈ s, u i)) * (((v x)^2+1)^2 * D (∑ i ∈ s, v i)) := by ring
      _ ≤ 5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i))
            * (5^(u x) * D (u x + ∑ i ∈ s, u i)) * (5^(v x) * D (v x + ∑ i ∈ s, v i)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (keyK (u x) (∑ i ∈ s, u i)))
            (keyK (v x) (∑ i ∈ s, v i))
      _ = 5^((u x + ∑ i ∈ s, u i) + (v x + ∑ i ∈ s, v i))
            * D (u x + ∑ i ∈ s, u i) * D (v x + ∑ i ∈ s, v i) := by ring

lemma pow4_le (a b : ℕ) (h : a^4 ≤ b^4) : a ≤ b := by
  by_contra hc
  exact absurd h (not_le.mpr (Nat.pow_lt_pow_left (Nat.lt_of_not_le hc) (by norm_num)))

/-- The block optimum. -/
theorem blockBound (s : Finset α) (u v : α → ℕ) (n : ℕ)
    (hu : (∑ i ∈ s, u i) ≤ n) (hv : (∑ i ∈ s, v i) ≤ n) :
    (Even n → (∏ i ∈ s, (u i * v i + 1)) ≤ 5^(n/2)) ∧
    (Odd n → (∏ i ∈ s, (u i * v i + 1)) ≤ 2 * 5^((n-1)/2)) := by
  have hP := potentialF s u v
  set p := ∑ i ∈ s, u i
  set q := ∑ i ∈ s, v i
  set P := ∏ i ∈ s, (u i * v i + 1)
  constructor
  · rintro ⟨k, hk⟩
    have h1 : 25 * P^4 ≤ 5^(p+q) * 25 := by
      calc 25 * P^4 ≤ 5^(p+q) * D p * D q := hP
        _ ≤ 5^(p+q) * 5 * 5 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (D_le p)) (D_le q)
        _ = 5^(p+q) * 25 := by ring
    have h2 : P^4 ≤ 5^(p+q) := by omega
    have h3 : P^4 ≤ 5^(4*k) := le_trans h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : (5^k)^4 = 5^(4*k) := by rw [← pow_mul]; ring_nf
    have hle : P ≤ 5^k := pow4_le _ _ (by rw [h4]; exact h3)
    have hnk : n/2 = k := by omega
    rw [hnk]; exact hle
  · rintro ⟨k, hk⟩
    have hgoal : P^4 ≤ 16 * 5^(4*k) := by
      by_cases hcase : p + q ≤ 4*k+1
      · have h1 : 25 * P^4 ≤ 5^(p+q) * 25 := by
          calc 25 * P^4 ≤ 5^(p+q) * D p * D q := hP
            _ ≤ 5^(p+q) * 5 * 5 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (D_le p)) (D_le q)
            _ = 5^(p+q) * 25 := by ring
        have h2 : P^4 ≤ 5^(p+q) := by omega
        calc P^4 ≤ 5^(4*k+1) := le_trans h2 (Nat.pow_le_pow_right (by norm_num) hcase)
          _ = 5 * 5^(4*k) := by ring
          _ ≤ 16 * 5^(4*k) := Nat.mul_le_mul_right _ (by norm_num)
      · have hpn : p = n := by omega
        have hqn : q = n := by omega
        have hodd : n % 2 = 1 := by omega
        have hDp : D p = 4 := by rw [hpn]; exact D_odd hodd
        have hDq : D q = 4 := by rw [hqn]; exact D_odd hodd
        have h1 : 25 * P^4 ≤ 5^(p+q) * 4 * 4 := by rw [hDp, hDq] at hP; exact hP
        have hpq2 : p + q = 4*k+2 := by omega
        have h2 : 5^(p+q) * 4 * 4 = 25 * (16 * 5^(4*k)) := by rw [hpq2]; ring
        omega
    have h4 : (2*5^k)^4 = 16 * 5^(4*k) := by
      have e : (5^k)^4 = 5^(4*k) := by rw [← pow_mul]; ring_nf
      calc (2*5^k)^4 = 16 * (5^k)^4 := by ring
        _ = 16 * 5^(4*k) := by rw [e]
    have hle : P ≤ 2*5^k := pow4_le _ _ (by rw [h4]; exact hgoal)
    have hnk : (n-1)/2 = k := by omega
    rw [hnk]; exact hle

end Arith

/-! ## The bridge: a `G`-invariant system is an exact coset cover of `G ∖ {1}` -/

open CosetCover Finset MulAction

section GIB
variable {G X : Type} [CommGroup G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
variable {A B : G → Finset X}

/-- Index type of the cover: pairs `(x, y)` with `x ∈ A 1`, `y ∈ B 1`, in the same orbit. -/
abbrev Idx (A B : G → Finset X) : Type :=
  {q : X × X // q.1 ∈ A 1 ∧ q.2 ∈ B 1 ∧ ∃ d : G, d⁻¹ • q.1 = q.2}

noncomputable instance instFintypeIdx : Fintype (Idx A B) := Fintype.ofFinite _

lemma smul_mem_iff (hB : ∀ k g : G, B (k * g) = (B g).image (fun x => k • x))
    (g : G) (x : X) : x ∈ B g ↔ g⁻¹ • x ∈ B 1 := by
  have h : B g = (B 1).image (fun z => g • z) := by have := hB g 1; simpa using this
  rw [h, Finset.mem_image]
  exact ⟨by rintro ⟨z, hz, rfl⟩; simpa using hz, fun h => ⟨g⁻¹ • x, h, by simp⟩⟩

/-- Stabilisers are constant on orbits. Commutativity of `G` is used here. -/
lemma stab_smul (g : G) (x : X) : stabilizer G (g • x) = stabilizer G x := by
  ext h
  simp only [mem_stabilizer_iff]
  constructor
  · intro hh
    have h1 : (h * g) • x = g • x := by rw [mul_smul]; exact hh
    have h2 : (g * h) • x = g • x := by rwa [mul_comm] at h1
    rw [mul_smul] at h2
    exact (MulAction.injective g) h2
  · intro hh; rw [← mul_smul, mul_comm, mul_smul, hh]

/-- `{g | g⁻¹ • x = y}` is the left coset `d₀ · stabilizer G x`. Commutativity again. -/
lemma dict (x y : X) (d0 g : G) (hd0 : d0⁻¹ • x = y) :
    (d0⁻¹ * g ∈ stabilizer G x) ↔ g⁻¹ • x = y := by
  constructor
  · intro h
    have hinv : (d0⁻¹ * g)⁻¹ ∈ stabilizer G x := (Subgroup.inv_mem_iff _).mpr h
    have e : (d0⁻¹ * g)⁻¹ = d0 * g⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
    rw [e] at hinv
    rw [mem_stabilizer_iff, mul_smul] at hinv
    rw [← hd0]
    calc g⁻¹ • x = d0⁻¹ • (d0 • (g⁻¹ • x)) := by rw [inv_smul_smul]
      _ = d0⁻¹ • x := by rw [hinv]
  · intro h
    have h' : g⁻¹ • x = d0⁻¹ • x := by rw [h, ← hd0]
    have h2 : (d0 * g⁻¹) • x = x := by rw [mul_smul, h', smul_inv_smul]
    have hm : (d0 * g⁻¹) ∈ stabilizer G x := by rw [mem_stabilizer_iff]; exact h2
    have e : (d0 * g⁻¹)⁻¹ = d0⁻¹ * g := by rw [mul_inv_rev, inv_inv, mul_comm]
    have := (Subgroup.inv_mem_iff _).mpr hm
    rwa [e] at this

/-- The chosen coset representative for the part named by `i`. -/
noncomputable def bs (i : Idx A B) : G := Classical.choose i.2.2.2
lemma bs_spec (i : Idx A B) : (bs i)⁻¹ • i.1.1 = i.1.2 := Classical.choose_spec i.2.2.2

lemma memb (i : Idx A B) (z : Additive G) :
    (z - Additive.ofMul (bs i) ∈ Subgroup.toAddSubgroup (stabilizer G i.1.1))
      ↔ (Additive.toMul z)⁻¹ • i.1.1 = i.1.2 := by
  have hx : Additive.toMul (z - Additive.ofMul (bs i)) = (bs i)⁻¹ * Additive.toMul z := by
    simp [div_eq_mul_inv, mul_comm]
  rw [Additive.mem_toAddSubgroup, hx]
  exact dict _ _ (bs i) _ (bs_spec i)

variable (A B)

/-- **The bridge.**  An abelian-group-invariant `1`-cross intersecting set pair system yields
an exact coset cover of `G ∖ {1}`, the part named by `(x, y)` being `{g | g⁻¹ • x = y}`, a left
coset of `stabilizer G x`. -/
noncomputable def coverOf
    (hB : ∀ k g : G, B (k * g) = (B g).image (fun x => k • x))
    (hAB : ∀ g : G, A g ∩ B g = ∅)
    (hcross : ∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) :
    ExactCosetCover (Additive G) (Idx A B) where
  base := fun i => Additive.ofMul (bs i)
  sub := fun i => Subgroup.toAddSubgroup (stabilizer G i.1.1)
  disj := by
    rintro i j hij z ⟨h1, h2⟩
    set g : G := Additive.toMul z with hg
    have m1 : g⁻¹ • i.1.1 = i.1.2 := (memb i z).1 h1
    have m2 : g⁻¹ • j.1.1 = j.1.2 := (memb j z).1 h2
    have hgne : g ≠ 1 := by
      intro h
      rw [h] at m1
      have heq : i.1.1 = i.1.2 := by simpa using m1
      have hmem : i.1.1 ∈ A 1 ∩ B 1 := Finset.mem_inter.2 ⟨i.2.1, by rw [heq]; exact i.2.2.1⟩
      rw [hAB 1] at hmem
      simp at hmem
    have hxi : i.1.1 ∈ A 1 ∩ B g := Finset.mem_inter.2 ⟨i.2.1,
      (smul_mem_iff hB g i.1.1).2 (by rw [m1]; exact i.2.2.1)⟩
    have hxj : j.1.1 ∈ A 1 ∩ B g := Finset.mem_inter.2 ⟨j.2.1,
      (smul_mem_iff hB g j.1.1).2 (by rw [m2]; exact j.2.2.1)⟩
    have hcard := hcross 1 g (Ne.symm hgne)
    have hxx : i.1.1 = j.1.1 := Finset.card_le_one.1 (le_of_eq hcard) _ hxi _ hxj
    apply hij
    apply Subtype.ext
    apply Prod.ext hxx
    rw [← m1, ← m2, hxx]
  covers := by
    intro z
    constructor
    · intro hz
      set g : G := Additive.toMul z with hg
      have hgne : g ≠ 1 := by
        intro h
        exact hz (Additive.toMul.injective h)
      have hcard := hcross 1 g (Ne.symm hgne)
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
      have hxm : x ∈ A 1 ∩ B g := by rw [hx]; exact Finset.mem_singleton_self x
      obtain ⟨hxA, hxB⟩ := Finset.mem_inter.1 hxm
      have hy : g⁻¹ • x ∈ B 1 := (smul_mem_iff hB g x).1 hxB
      exact ⟨⟨(x, g⁻¹ • x), hxA, hy, ⟨g, rfl⟩⟩, (memb _ z).2 rfl⟩
    · rintro ⟨i, hi⟩ rfl
      have m1 : (Additive.toMul (0 : Additive G))⁻¹ • i.1.1 = i.1.2 := (memb i 0).1 hi
      have heq : i.1.1 = i.1.2 := by simpa using m1
      have hmem : i.1.1 ∈ A 1 ∩ B 1 := Finset.mem_inter.2 ⟨i.2.1, by rw [heq]; exact i.2.2.1⟩
      rw [hAB 1] at hmem
      simp at hmem

end GIB

/-! ## Counting: the multiplicities are dominated by the per-stabiliser block products -/

section Counting
open Finset MulAction
variable {G X : Type} [CommGroup G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
variable {A B : G → Finset X}

open Classical in
theorem mult_le (K : Subgroup G) :
    (Finset.univ.filter (fun i : Idx A B => stabilizer G i.1.1 = K)).card
      ≤ ((A 1).filter (fun x => stabilizer G x = K)).card
        * ((B 1).filter (fun y => stabilizer G y = K)).card := by
  classical
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i : Idx A B => stabilizer G i.1.1 = K),
      i.1 ∈ ((A 1).filter (fun x => stabilizer G x = K)) ×ˢ
             ((B 1).filter (fun y => stabilizer G y = K)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨d, hd⟩ := i.2.2.2
    have hstaby : stabilizer G i.1.2 = K := by rw [← hd, stab_smul]; exact hi
    exact Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨i.2.1, hi⟩, Finset.mem_filter.2 ⟨i.2.2.1, hstaby⟩⟩
  have := Finset.card_le_card_of_injOn (fun i : Idx A B => i.1) hmaps
    (fun i _ j _ h => Subtype.ext h)
  simpa [Finset.card_product] using this

open Classical in
theorem sum_alpha (T : Finset (Subgroup G)) (hT : ∀ x ∈ A 1, stabilizer G x ∈ T) :
    ∑ K ∈ T, ((A 1).filter (fun x => stabilizer G x = K)).card = (A 1).card :=
  (Finset.card_eq_sum_card_fiberwise hT).symm

open Classical in
theorem sum_beta_le (T : Finset (Subgroup G)) :
    ∑ K ∈ T, ((B 1).filter (fun y => stabilizer G y = K)).card ≤ (B 1).card := by
  classical
  set s := (B 1).filter (fun y => stabilizer G y ∈ T) with hs
  have hmaps : ∀ y ∈ s, stabilizer G y ∈ T := fun y hy => (Finset.mem_filter.1 hy).2
  have h1 : s.card = ∑ K ∈ T, (s.filter (fun y => stabilizer G y = K)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ K ∈ T, s.filter (fun y => stabilizer G y = K)
      = (B 1).filter (fun y => stabilizer G y = K) := by
    intro K hK
    ext y
    simp only [hs, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hy, -⟩, hk⟩
      exact ⟨hy, hk⟩
    · rintro ⟨hy, hk⟩
      exact ⟨⟨hy, by rw [hk]; exact hK⟩, hk⟩
  rw [Finset.sum_congr rfl (fun K hK => by rw [h2 K hK])] at h1
  rw [← h1]
  exact Finset.card_le_card (Finset.filter_subset _ _)

end Counting

/-! ## The theorem -/

open CosetCover Finset MulAction

theorem proof :
    ∀ (G X : Type) [CommGroup G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
      (n : ℕ) (A B : G → Finset X),
      (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
      (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
      (∀ g : G, (A g).card ≤ n) →
      (∀ g : G, (B g).card ≤ n) →
      (∀ g : G, A g ∩ B g = ∅) →
      (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
        (Even n → Fintype.card G ≤ 5 ^ (n / 2)) ∧
        (Odd n → Fintype.card G ≤ 2 * 5 ^ ((n - 1) / 2)) := by
  intro G X _ _ _ _ _ n A B _hA hB hcA hcB hAB hcross
  classical
  set P := coverOf A B hB hAB hcross with hP
  have hLC : Fintype.card (Additive G) ≤ ∏ K ∈ P.used, (P.mult K + 1) :=
    ExactCosetCover.lemmaC_holds P
  set T : Finset (Subgroup G) := (A 1).image (fun x => stabilizer G x) with hT
  have hTmem : ∀ x ∈ A 1, stabilizer G x ∈ T := fun x hx => Finset.mem_image_of_mem _ hx
  have hsub : P.used ⊆ T.image Subgroup.toAddSubgroup := by
    intro K' hK'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hK'
    exact Finset.mem_image.2 ⟨stabilizer G i.1.1, hTmem _ i.2.1, rfl⟩
  have hmulteq : ∀ K : Subgroup G,
      P.mult (Subgroup.toAddSubgroup K)
        = (Finset.univ.filter (fun i : Idx A B => stabilizer G i.1.1 = K)).card := by
    intro K
    unfold ExactCosetCover.mult ExactCosetCover.fiber
    congr 1
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h; exact Subgroup.toAddSubgroup.injective h
    · intro h; exact congrArg Subgroup.toAddSubgroup h
  have hcard : Fintype.card G ≤ ∏ K ∈ T,
      (((A 1).filter (fun x => stabilizer G x = K)).card
        * ((B 1).filter (fun y => stabilizer G y = K)).card + 1) := by
    calc Fintype.card G
        = Fintype.card (Additive G) := Fintype.card_congr (Additive.ofMul)
      _ ≤ ∏ K ∈ P.used, (P.mult K + 1) := hLC
      _ ≤ ∏ K ∈ T.image Subgroup.toAddSubgroup, (P.mult K + 1) :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub
            (fun K _ _ => Nat.succ_le_succ (Nat.zero_le _))
      _ = ∏ K ∈ T, (P.mult (Subgroup.toAddSubgroup K) + 1) :=
          Finset.prod_image (fun a _ b _ h => Subgroup.toAddSubgroup.injective h)
      _ ≤ ∏ K ∈ T, (((A 1).filter (fun x => stabilizer G x = K)).card
            * ((B 1).filter (fun y => stabilizer G y = K)).card + 1) := by
          refine Finset.prod_le_prod' ?_
          intro K _
          rw [hmulteq K]
          exact Nat.succ_le_succ (mult_le K)
  have hblock := Arith.blockBound T
      (fun K => ((A 1).filter (fun x => stabilizer G x = K)).card)
      (fun K => ((B 1).filter (fun y => stabilizer G y = K)).card) n
      (by rw [sum_alpha T hTmem]; exact hcA 1)
      (le_trans (sum_beta_le T) (hcB 1))
  exact ⟨fun he => le_trans hcard (hblock.1 he), fun ho => le_trans hcard (hblock.2 ho)⟩

end Submissions.GroupInvariantAbelianFGK.AbelianCosetBridge
