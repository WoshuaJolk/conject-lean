import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# AbelianCayleySubgroupCut — maximal connectivity of abelian Cayley graphs from subgroup
boundaries, and nothing more

The grouping layer (s=33, s=35) needs maximal vertex connectivity of specific graphs, and the
tool proposed for it is Hamidoune's atom theory: in a connected Cayley graph on a finite
abelian group, the atom containing the identity is a subgroup, so a connectivity defect
`κ < δ` is always witnessed by a proper nontrivial subgroup whose boundary is smaller than the
degree. Contrapositively — and this is the usable form — **if every proper nontrivial subgroup
has boundary at least `|S|`, the Cayley graph is maximally connected**.

**Scope discipline, recorded up front.** This is a statement about CAYLEY graphs only. It
covers the connected circulant seed of s=35 (a Cayley graph on `Z_m`), the seed's complement
(again circulant), any class that is a union of difference classes, and the deficient
`Z_6 × Z_2` examples recorded in the s=34 message — whose minimum cuts are literally index-2
subgroups, exactly as the atom theorem predicts. It does NOT cover the class complements of
the s=35 design: those are the seed together with unions of one-factors of `K_m` minus the
seed, which are not Cayley graphs, so the subgroup dichotomy is not available for them — for
those graphs the hypothesis has to be earned by other structure, and no downstream use may
apply this statement to them. That restriction is the point of filing this shape rather than
a blanket `κ = δ` claim; the blanket versions are refuted on this board (`r`-regular graphs
with `κ = r − 1` exist for every `r ≤ n − 3`, s=34/s=35 messages).

**Reading the formalisation.** The Cayley graph on `G` with symmetric connection set `S`
(`0 ∉ S`) is `SimpleGraph.fromRel (fun a b => a - b ∈ S)`. A subgroup is presented as a
`Finset` containing `0`, closed under addition and negation; nontrivial means `≠ {0}`, proper
means `≠ univ`. The boundary of `H` is `(H + S) \ H`, written with `biUnion`/`image`. Maximal
connectivity is stated in deletion form, as in `RoundRobinUnionConnectivity`: removing fewer
than `|S|` vertices leaves the induced graph connected. No connectedness hypothesis is needed:
if `S` fails to generate `G`, the subgroup it generates is proper with empty boundary, so the
hypothesis is unsatisfiable and the claim is vacuous there.
-/

namespace Statements.AbelianCayleySubgroupCut

abbrev statement : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
    ∀ S : Finset G, (∀ s ∈ S, -s ∈ S) → (0 : G) ∉ S →
      (∀ H : Finset G, (0 : G) ∈ H →
        (∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) → (∀ a ∈ H, -a ∈ H) →
        H ≠ {0} → H ≠ Finset.univ →
        S.card ≤ ((H.biUnion fun h => S.image fun s => h + s) \ H).card) →
      ∀ X : Finset G, X.card < S.card →
        ((SimpleGraph.fromRel (fun a b => a - b ∈ S)).induce {v : G | v ∉ X}).Connected

theorem target : statement := sorry

end Statements.AbelianCayleySubgroupCut
