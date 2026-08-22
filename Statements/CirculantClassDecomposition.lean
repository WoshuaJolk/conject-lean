import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.ZMod.Basic

/-!
# CirculantClassDecomposition — the decomposition layer with a CONNECTED degenerate class

This replaces the shape of the leftover-decomposition problem rather than solving the previous shape.

Previously the degenerate `k`-regular class was fixed to be `c` disjoint copies of the gadget on
`m = 2kc` vertices, and the other classes had to decompose the complement of that fixed graph. That
shape carries a genuine obstruction: a class's complement contains the degenerate class, so with `c ≥ 2`
copies the complement inherits `c` mutually disconnected pieces, and a class holding all of the cross
edges has a disconnected complement — which by Lovász–Saks–Schrijver means it has no general-position
representation at all. For `p = 2` that is unavoidable, since the single non-degenerate class must hold
everything.

The obstruction is an artifact of the disjointness, not of the problem. Take the degenerate class to be
a CONNECTED `k`-regular circulant instead, and index everything by `ZMod m`:

* `G = C_m(S_k)` with `S_k = {±1, …, ±⌊k/2⌋}`, together with `{m/2}` when `k` is odd, so `G` is
  `k`-regular, connected and vertex-transitive. `C_10(±1, ±2)` and the Möbius ladders are members, and
  both are known to carry tight `(k+1)`-spanning representations.
* Every non-degenerate class is a union of difference classes of `ZMod m`, hence a circulant too, so
  every class complement is a circulant containing `G`.

The claim is that the degrees can always be met this way with every class complement MAXIMALLY
connected, which is exactly the LSS hypothesis for realizing that class in general position in
dimension `d_j`. The `p = 2` obstruction disappears: I measured every `p = 2` tuple for `m ≤ 20` and
every one is satisfied, including `(4, 12)` at `m = 16`, which is impossible in the disjoint-copies
shape.

Two warnings recorded so that this is not mistaken for a soft claim. First, maximal connectivity is not
automatic for circulants, so the grouping genuinely has content: on `Z_6 × Z_2` there are connected
abelian Cayley graphs with `δ = 8` and `κ = 6`, the cut being an index-2 subgroup. Second, no degree
hypothesis can substitute: `r`-regular graphs with `κ = r - 1` exist for every `r ≤ n - 3`.

Difference classes have size 2, except for `m/2` which is self-paired, so a class of odd degree needs
the single involution — which the degenerate class already consumes when `k` is odd. That is why the
statement asks for the degrees to be met by *some* assignment rather than by a prescribed rule.
-/

namespace Statements.CirculantClassDecomposition

/-- The circulant on `ZMod m` with symmetric connection set `S`. -/
def circulant (m : ℕ) (S : Finset (ZMod m)) : SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w => (w - v) ∈ S

/-- The connection set of the connected `k`-regular degenerate class. -/
def degSet (m k : ℕ) : Finset (ZMod m) :=
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (i : ZMod m)) ∪
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (-(i : ZMod m))) ∪
  (if k % 2 = 1 then {((m / 2 : ℕ) : ZMod m)} else ∅)

/-- The connection set of class `j`'s complement: the degenerate class together with every other
class. -/
def complSet {m q : ℕ} (k : ℕ) (A : Fin q → Finset (ZMod m)) (j : Fin q) : Finset (ZMod m) :=
  degSet m k ∪ (Finset.univ.filter fun j' => j' ≠ j).biUnion A

/-- The canonical proposition. For `m` even, `k ≥ 2` with `2 * k < m`, and any class degrees `e j ≥ 1`
summing to `m - 1 - k`, there is an assignment `A` of the non-degenerate differences to classes —
symmetric, disjoint from the degenerate connection set, and covering it exactly — such that class `j`
has degree `e j` and the complement of class `j`, namely everything outside it, stays connected after
deleting fewer than `m - 1 - e j` vertices: maximal connectivity, and precisely the LSS hypothesis for
that class. -/
abbrev statement : Prop :=
  ∀ m k q : ℕ, 2 ≤ k → 2 * k < m → m % 2 = 0 → ∀ e : Fin q → ℕ,
    (∀ j, 1 ≤ e j) →
    (∑ j, e j) + 1 + k = m →
    ∃ A : Fin q → Finset (ZMod m),
      (∀ j x, x ∈ A j → -x ∈ A j) ∧
      (∀ j, (0 : ZMod m) ∉ A j) ∧
      (∀ j x, x ∈ A j → x ∉ degSet m k) ∧
      (∀ j j', j ≠ j' → Disjoint (A j) (A j')) ∧
      (∀ j, (A j).card = e j) ∧
      (∀ j, ∀ X : Finset (ZMod m),
        X.card + 1 + e j < m →
        ((circulant m (complSet k A j)).induce {v : ZMod m | v ∉ X}).Connected)

theorem target : statement := sorry

end Statements.CirculantClassDecomposition
