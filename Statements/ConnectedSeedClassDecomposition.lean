import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.ZMod.Basic

/-!
# ConnectedSeedClassDecomposition — the decomposition layer, corrected twice

This is the honest form of the layer, and it supersedes `CirculantClassDecomposition`, which is FALSE as
stated. Both corrections are recorded here because each was found by measurement rather than by thought.

**Correction 1, to the disjoint-copies shape.** Fixing the degenerate `k`-regular class to be `c` copies
of a `2k`-vertex gadget makes every class complement inherit `c` mutually disconnected pieces, so a
class holding all cross edges has a disconnected complement and — LSS being an iff — no general-position
representation at all. Unavoidable for `p = 2`. Taking the degenerate class CONNECTED removes this: with
a connected circulant seed, every `p = 2` tuple up to `m = 20` is satisfied, including `(4, 12)` at
`m = 16`, which is impossible with copies.

**Correction 2, to the all-circulant shape.** Restricting the non-degenerate classes to unions of
difference classes of `ZMod m` is too rigid, in two independent ways, both exact:

* *Parity.* Difference classes have size 2 except the single involution `m / 2`, which the degenerate
  class already consumes when `k` is odd. So a class of ODD degree usually cannot be a circulant at all,
  and 1134 of the 1453 audited cases at `m ≤ 16` fail for this reason alone — every one of them with an
  odd class degree present.
* *Connectivity.* Even when the degrees can be met, some forced class is deficient: at `m = 12` with
  `k = 3` and four classes of degree 2, each class must be a single difference pair, and the pair
  `{3, 9}` is forced; its complement has `δ = 9` but `κ = 8`, with cut `{0,1,3,4,6,7,9,10}`. 22 further
  audited cases fail this way.

So the classes must be allowed to be arbitrary regular graphs — unions of one-factors of `K_m - G` — with
only the degenerate class circulant. That is what is stated below. `K_m - G` is `(m - 1 - k)`-regular on
an even number of vertices, and `m - 1 - k ≥ m / 2` whenever `k < m / 2`, so its one-factorizability is
the published 1-factorization conjecture regime (Chetwynd–Hilton; Csaba–Kühn–Lo–Osthus–Treglown for
large `m`) rather than something to be assumed.

What remains genuinely open is the grouping: 297 audited cases at `m ≤ 16` do admit a valid grouping, but
maximal connectivity is not forced by degree — `r`-regular graphs with `κ = r - 1` exist for every
`r ≤ n - 3` — nor by being a Cayley graph, since `Z_6 × Z_2` carries connected Cayley graphs with
`δ = 8`, `κ = 6`, cut by an index-2 subgroup.
-/

namespace Statements.ConnectedSeedClassDecomposition

/-- The circulant on `ZMod m` with symmetric connection set `S`. -/
def circulant (m : ℕ) (S : Finset (ZMod m)) : SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w => (w - v) ∈ S

/-- Connection set of the connected `k`-regular degenerate class: `{±1, …, ±⌊k/2⌋}`, together with the
involution `m / 2` when `k` is odd. -/
def degSet (m k : ℕ) : Finset (ZMod m) :=
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (i : ZMod m)) ∪
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (-(i : ZMod m))) ∪
  (if k % 2 = 1 then {((m / 2 : ℕ) : ZMod m)} else ∅)

/-- The canonical proposition. Let `G` be the connected `k`-regular circulant seed on `ZMod m`, and let
`e j ≥ 1` be class degrees summing to `m - 1 - k`. Then the edges outside `G` can be dealt out to the
classes — `cls j` being class `j`, each `e j`-regular, pairwise edge-disjoint, and together covering
exactly the non-edges of `G` — so that every class complement (`G` together with the other classes)
remains connected after deleting fewer than `m - 1 - e j` vertices: maximal connectivity, and precisely
the Lovász–Saks–Schrijver hypothesis for realizing class `j` in general position in dimension
`d j = e j + 1`. -/
abbrev statement : Prop :=
  ∀ m k q : ℕ, 2 ≤ k → 2 * k < m → m % 2 = 0 → ∀ e : Fin q → ℕ,
    (∀ j, 1 ≤ e j) →
    (∑ j, e j) + 1 + k = m →
    ∃ cls : Fin q → SimpleGraph (ZMod m),
      (∀ j v, ∃ N : Finset (ZMod m), N.card = e j ∧ ∀ w, (cls j).Adj v w ↔ w ∈ N) ∧
      (∀ j v w, (cls j).Adj v w → ¬ (circulant m (degSet m k)).Adj v w) ∧
      (∀ j j' v w, j ≠ j' → (cls j).Adj v w → ¬ (cls j').Adj v w) ∧
      (∀ v w, v ≠ w → ¬ (circulant m (degSet m k)).Adj v w → ∃ j, (cls j).Adj v w) ∧
      (∀ j : Fin q, ∀ X : Finset (ZMod m),
        X.card + 1 + e j < m →
        (((circulant m (degSet m k)) ⊔ (⨆ j' ∈ {j' : Fin q | j' ≠ j}, cls j')).induce
            {v : ZMod m | v ∉ X}).Connected)

theorem target : statement := sorry

end Statements.ConnectedSeedClassDecomposition
