import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lovász's theta function of a complement, and the Paley 1-localization

Shared vocabulary for the localization programme around the clique number of the Paley
graph (Bandeira–Dmitriev, *Randomstrasse101: Open Problems of 2025*, Problems 25–29).

Two independent pieces of vocabulary live here.

* `Commons.thetaClique adj` is Lovász's `ϑ` of the **complement** of the graph with
  adjacency relation `adj` — the standard semidefinite upper bound on the *clique* number
  of `adj`.  It is `ϑ(Ḡ)` in Lovász's own notation (*On the Shannon capacity of a graph*,
  IEEE Trans. Inform. Theory **25** (1979), Theorem 4): the maximum of `∑ᵤ∑ᵥ Xᵤᵥ` over
  positive semidefinite `X` of trace `1` whose entries vanish on the edges of the
  complement, i.e. on the **non-adjacent** distinct pairs of `adj`.  Writing the zero
  pattern on the non-edges rather than the edges is exactly what turns the independence
  bound into the clique bound; `thetaClique adj ≥ ω(adj)`.

* `Commons.paleyLocAdj p` is the **1-localization of the Paley graph** on `ZMod p`: the
  subgraph induced on the neighbourhood of the vertex `0`, i.e. on the nonzero squares,
  two of them joined when their difference is again a nonzero square.

## Design notes, for reading the definitions back against the informal statements

* The vertex type is the nonzero squares of `ZMod p`, which for `p` an odd prime has
  exactly `(p-1)/2` elements.  It is `N(0)` in the Paley graph, so `thetaClique
  (paleyLocAdj p)` is the localized bound, and `ω(Paley p) ≤ 1 + thetaClique
  (paleyLocAdj p)`.

* `paleyLocAdj p u v` says only that `u - v` is a nonzero square.  Irreflexivity is then
  automatic (`u - u = 0` is not a *nonzero* square).  Symmetry holds precisely when `-1`
  is a square mod `p`, i.e. when `p ≡ 1 (mod 4)`, which is the hypothesis under which the
  Paley graph is a graph at all; nothing here assumes it, and statements that need it
  carry it explicitly.

* `thetaClique` is defined as a supremum over a set of reals.  That set is nonempty
  whenever the vertex type is (take `X` diagonal with entries `1/n`) and is bounded above
  by the number of vertices (for `X` positive semidefinite of trace `1`,
  `1ᵀ X 1 ≤ n · tr X`), so the supremum is the genuine optimal value rather than a junk
  value, on every vertex type that is nonempty.  On an **empty** vertex type the trace
  condition is unsatisfiable, the feasible set is empty and `sSup ∅ = 0` by Mathlib's
  convention; no statement here is about an empty vertex type.

* The program is stated over `ℝ` with symmetric `X`.  Lovász's `ϑ` is usually written over
  `ℝ` for real graphs and this is the standard real form; `Matrix.PosSemidef` over `ℝ`
  already carries `IsHermitian`, hence symmetry of `X`.
-/

namespace Commons

section Theta

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The feasible values of the Lovász semidefinite program for the complement of `adj`:
all `∑ᵤ∑ᵥ Xᵤᵥ` for `X` positive semidefinite, of trace `1`, vanishing on every
**non-adjacent** distinct pair. -/
def thetaCliqueFeasible (adj : V → V → Prop) : Set ℝ :=
  { s : ℝ | ∃ X : Matrix V V ℝ,
      X.PosSemidef ∧ X.trace = 1 ∧
      (∀ u v : V, u ≠ v → ¬ adj u v → X u v = 0) ∧
      s = ∑ u : V, ∑ v : V, X u v }

/-- `thetaClique adj` is Lovász's `ϑ` of the complement of `adj`: the optimum of the
semidefinite program `thetaCliqueFeasible`.  It upper-bounds the clique number of `adj`. -/
noncomputable def thetaClique (adj : V → V → Prop) : ℝ :=
  sSup (thetaCliqueFeasible adj)

end Theta

section Paley

/-- `x` is a nonzero square in `ZMod p`. -/
def IsNonzeroSq {p : ℕ} (x : ZMod p) : Prop := x ≠ 0 ∧ ∃ r : ZMod p, x = r * r

instance {p : ℕ} [NeZero p] (x : ZMod p) : Decidable (IsNonzeroSq x) := by
  unfold IsNonzeroSq; infer_instance

/-- The vertex set of the Paley 1-localization: the nonzero squares of `ZMod p`, which is
the neighbourhood of `0` in the Paley graph.  Reducible, so that the `Fintype`,
`DecidableEq` and coercion instances of the underlying subtype apply directly. -/
abbrev PaleyLocV (p : ℕ) [NeZero p] : Type := {x : ZMod p // IsNonzeroSq x}

/-- Adjacency of the Paley 1-localization: two nonzero squares are joined when their
difference is a nonzero square. -/
def paleyLocAdj (p : ℕ) [NeZero p] : PaleyLocV p → PaleyLocV p → Prop :=
  fun u v => IsNonzeroSq ((u : ZMod p) - (v : ZMod p))

instance (p : ℕ) [NeZero p] (u v : PaleyLocV p) : Decidable (paleyLocAdj p u v) := by
  unfold paleyLocAdj; infer_instance

/-- `paleyLocTheta p hp` is `ϑ` of the complement of the Paley 1-localization mod `p`:
the semidefinite upper bound on the clique number of `G_{p,1}`, hence
`ω(Paley p) ≤ 1 + paleyLocTheta p hp`. -/
noncomputable def paleyLocTheta (p : ℕ) (hp : 0 < p) : ℝ :=
  haveI : NeZero p := NeZero.of_pos hp
  thetaClique (paleyLocAdj p)

end Paley

end Commons
