import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.ZMod.Basic

/-!
# GroupingSpreadingCrossFirst — cross-first spreading yields LSS-ready class complements

Companion residual of `ConnectedSeedClassDecomposition` (the honest decomposition layer) and
`GadgetComplementGrouping` (the disjoint-copies leftover shape). Those statements ask for a
grouping of one-factors of `K_m` minus the seed such that every class complement is
`(m - d_j)`-connected — the Lovász–Saks–Schrijver hypothesis. Exact measurement finds such a
grouping in **9455 / 9455** audited cases through `m = 22`. This statement isolates the
*constructive* half: from any 1-factorization of the seed complement, a **cross-first spreading**
assignment of factors to classes makes every class complement maximally connected.

## Two hard-won constraints

**Within-first fails.** A greedy rule that fills each class with factors lying inside the cosets of
a prospective cut (the index-2 subgroup of `ZMod m`, or the copies of a disconnected seed) is *not*
sufficient: hard audits fail under that rule. The rule that settles them is **cross-first
spreading**: the factors that cross each prospective cut are dealt round-robin across classes
*first*, and only then are the within-cut factors used to top up degrees.

**Cayley buys nothing, and Hamidoune does not apply off the shelf.** Connected Cayley graphs need
not be optimally connected: `ZMod 6 × ZMod 2` carries examples with `δ = 8` and `κ = 6`, the cut
being an index-2 subgroup. Hamidoune's atom theorem — a positive atom through the identity of a
*Cayley* graph is a subgroup — therefore applies to the **seed** (which is circulant) and to any
piece that is genuinely Cayley. In the corrected design the non-degenerate **classes** are arbitrary
unions of one-factors of `K_m` minus the seed, and their **complements** inherit that generality:
they are not Cayley in general. So "every `κ < δ` defect is a proper subgroup cut" is **not**
available for class complements, and must not be claimed. (That overreach is exactly what
`CirculantClassDecomposition` already retracted.) Connectivity of the class complements has to be
proved directly from the spreading construction — or else the statement restricted to a Cayley
subcase and every downstream use restricted with it. This statement takes the direct route: the
conclusion is deletion-connectedness, not a subgroup-neighbourhood bound.

## What this statement claims

Fix even `m`, a connected `k`-regular circulant seed as in `ConnectedSeedClassDecomposition`, and
a 1-factorization of the complement. There is an assignment of those factors to classes of sizes
`e j` — the one produced by cross-first spreading — such that each class complement stays connected
after deleting fewer than `m - 1 - e j` vertices. That is maximal connectivity, and precisely the
LSS hypothesis for class `j`.

Scope. The 1-factorization itself is not constructed here. No blanket "degree ⇒ κ" or "Cayley ⇒ κ"
assertion is made. Hamidoune is **not** used in the conclusion; it remains available as a tool for
the seed and for any Cayley subcase carved out separately.
-/

namespace Statements.GroupingSpreadingCrossFirst

/-- The circulant on `ZMod m` with symmetric connection set `S`. -/
def circulant (m : ℕ) (S : Finset (ZMod m)) : SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w => (w - v) ∈ S

/-- Connection set of the connected `k`-regular seed. -/
def degSet (m k : ℕ) : Finset (ZMod m) :=
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (i : ZMod m)) ∪
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (-(i : ZMod m))) ∪
  (if k % 2 = 1 then {((m / 2 : ℕ) : ZMod m)} else ∅)

/-- A one-factor as an involution on `ZMod m` with no fixed points (perfect matching). -/
abbrev IsOneFactor {m : ℕ} (F : ZMod m → ZMod m) : Prop :=
  (∀ v, F (F v) = v) ∧ (∀ v, F v ≠ v)

/-- Class complement: the seed together with every factor not assigned to class `j`. -/
def classCompl {m n : ℕ} (k : ℕ) (F : Fin n → ZMod m → ZMod m) (g : Fin n → ℕ) (j : ℕ) :
    SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w =>
    (circulant m (degSet m k)).Adj v w ∨ ∃ t : Fin n, g t ≠ j ∧ F t v = w

/-- The canonical proposition.

For even `m`, `2 ≤ k`, `2 * k < m`, and class degrees `e j ≥ 1` summing to `m - 1 - k` with no
class taking every factor, every 1-factorization of the seed complement admits an assignment of its
factors to the classes — the cross-first spreading assignment — such that each class complement
stays connected after deleting fewer than `m - 1 - e j` vertices. -/
abbrev statement : Prop :=
  ∀ m k q : ℕ, 2 ≤ k → 2 * k < m → m % 2 = 0 → ∀ e : Fin q → ℕ,
    (∀ j, 1 ≤ e j) →
    (∑ j, e j) + 1 + k = m →
    (∀ j, e j + 1 < m - k) →
    ∀ n : ℕ, n = m - 1 - k →
    ∀ F : Fin n → ZMod m → ZMod m,
      (∀ t, IsOneFactor (F t)) →
      (∀ t v, ¬ (circulant m (degSet m k)).Adj v (F t v)) →
      (∀ v w, v ≠ w → ¬ (circulant m (degSet m k)).Adj v w → ∃! t, F t v = w) →
      ∃ g : Fin n → ℕ,
        (∀ j : Fin q, (Finset.univ.filter fun t => g t = (j : ℕ)).card = e j) ∧
        (∀ j : Fin q, ∀ X : Finset (ZMod m),
          X.card + 1 + e j < m →
          ((classCompl k F g (j : ℕ)).induce {v : ZMod m | v ∉ X}).Connected)

theorem target : statement := sorry

end Statements.GroupingSpreadingCrossFirst
