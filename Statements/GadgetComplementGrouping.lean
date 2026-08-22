import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# GadgetComplementGrouping — the grouping half of the leftover decomposition

Context, and why this is a separate claim. At `m = f_N + 1` the witness needs `E(K_m)` split into one
degenerate `k`-regular class, realized by the fixed gadget seed, and non-degenerate `(d_j - 1)`-regular
classes, each realized in general position in dimension `d_j`. Lovász–Saks–Schrijver supplies the
non-degenerate realizations, and its hypothesis for a class `H` is exactly that the complement of `H`
is `(m - d_j)`-connected. Since the class has degree `d_j - 1`, its complement has degree
`m - 1 - (d_j - 1) = m - d_j`, so the hypothesis is precisely that each complement attains **maximal**
vertex connectivity.

The companion statement `GadgetComplementOneFactorization` supplies the factors: the complement of the
`c` gadget copies is 1-factorizable into its `2kc - k - 1` factors, explicitly and with no search
(a `(j - i) mod k` colouring inside each copy, Laskar–Auerbach Hamiltonian cycles between copies). What
is *not* supplied by that statement is that the factors can be **grouped** into classes of the required
sizes with every class's complement maximally connected. That is this statement.

Why it is not automatic. `m - d_j ≥ m / 2` is equivalent to `d_j` not being dominant, so it is tempting
to invoke "an `r`-regular graph with `r ≥ n / 2` has `κ = r`". That is false: the 5-regular graph on
`{0, …, 9}` with edges `01 02 03 04 05 12 13 14 16 23 25 26 34 37 48 49 57 58 59 67 68 69 78 79 89`
has `κ = 4`, the cut being `{3, 4, 5, 6}`. So the grouping genuinely has to be constructed, and the
failure mode is visible in advance: the complement of a class *contains the gadget*, whose `c` copies
are mutually disconnected, so a class handed all of the cross factors has a complement with no edge
between copies at all. The rule that must therefore be proved is a spreading rule.

The hypothesis `e j + 1 < 2 * k * c - k` is not cosmetic, and marks a real boundary rather than a
convenience. If some class takes *every* factor its complement is exactly the gadget, which for `c ≥ 2`
is disconnected, so the conclusion fails outright. That happens precisely when there is only one
non-degenerate class, i.e. for `p = 2` — and the bipartite case is exactly where the classification is
already published (Chen–Johnston), so the LSS route being unavailable there is consistent rather than
alarming. Exact measurement over the exceptional tuples finds this to be the *only* failure: with the
hypothesis in force, every audited tuple admits a grouping.

Formalization. `F` is a 1-factorization as in `GadgetComplementOneFactorization`; `g` assigns each
factor to a class, with `e j` factors in class `j`; and class `j`'s complement is the gadget together
with every factor *not* assigned to `j`. Connectivity is spelled as deletion-connectedness — removing
fewer than `m - d_j` vertices leaves the graph connected — which is the same convention as
`RoundRobinUnionConnectivity` and avoids depending on a `κ` definition.
-/

namespace Statements.GadgetComplementGrouping

/-- Vertices of `m = 2kc` vectors: a gadget copy, a side (which of its two bases), and a position. -/
abbrev V (c k : ℕ) : Type := Fin c × Fin 2 × Fin k

/-- The degenerate class: `c` disjoint copies of two `K_k`s plus a perfect matching. -/
def gadget (c k : ℕ) : SimpleGraph (V c k) :=
  SimpleGraph.fromRel fun v w =>
    v.1 = w.1 ∧ ((v.2.1 = w.2.1 ∧ v.2.2 ≠ w.2.2) ∨ (v.2.1 ≠ w.2.1 ∧ v.2.2 = w.2.2))

/-- `K_m` minus the degenerate class. -/
def compl (c k : ℕ) : SimpleGraph (V c k) :=
  SimpleGraph.fromRel fun v w =>
    v.1 ≠ w.1 ∨ (v.1 = w.1 ∧ v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2)

/-- The complement of class `j`: the gadget, plus every factor assigned to another class. -/
def classCompl (c k n : ℕ) (F : Fin n → V c k → V c k) (g : Fin n → ℕ) (j : ℕ) :
    SimpleGraph (V c k) :=
  SimpleGraph.fromRel fun v w =>
    (gadget c k).Adj v w ∨ ∃ t : Fin n, g t ≠ j ∧ F t v = w

/-- The canonical proposition. For every `k ≥ 2`, every `c ≥ 1`, and every list of class degrees
`e j ≥ 1` summing to the factor count `2kc - k - 1`, none of which takes every factor, there is a
1-factorization of the complement of the gadget copies and an assignment of its factors to classes,
`e j` factors to class `j`, such that each class's complement stays connected after deleting fewer
than `m - d_j = m - 1 - e j` vertices — the Lovász–Saks–Schrijver hypothesis for that class. -/
abbrev statement : Prop :=
  ∀ k c q : ℕ, 2 ≤ k → 1 ≤ c → ∀ e : Fin q → ℕ,
    (∀ j, 1 ≤ e j) →
    (∑ j, e j) = 2 * k * c - k - 1 →
    (∀ j, e j + 1 < 2 * k * c - k) →
    ∃ (F : Fin (2 * k * c - k - 1) → V c k → V c k)
      (g : Fin (2 * k * c - k - 1) → ℕ),
      (∀ t v, (compl c k).Adj v (F t v)) ∧
      (∀ t v, F t (F t v) = v) ∧
      (∀ v w, (compl c k).Adj v w → ∃! t, F t v = w) ∧
      (∀ j : Fin q, (Finset.univ.filter fun t => g t = (j : ℕ)).card = e j) ∧
      (∀ j : Fin q, ∀ X : Finset (V c k),
        X.card + 1 + e j < 2 * k * c →
        ((classCompl c k _ F g (j : ℕ)).induce {v : V c k | v ∉ X}).Connected)

theorem target : statement := sorry

end Statements.GadgetComplementGrouping
