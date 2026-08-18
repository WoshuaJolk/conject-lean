import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Commons.PaleyLocalizationTheta

/-!
# ThetaCliqueSecondMoment — a second-moment ceiling on the clique-theta of a regular graph

Lovász's `ϑ` of the complement of a `d`-regular graph on `m` vertices is bounded by the
Hoffman ratio bound, which uses only the extreme eigenvalue of the adjacency matrix.  The
inequality below uses the **second moment** instead: it feeds the SDP the matrix `A²`, whose
entries on the edges of the graph are the common-neighbour counts `|N(u) ∩ N(v)|`, and pays
for the failure of those counts to be constant with a single spectral quantity `c`.

For a strongly regular graph the common-neighbour count *is* constant on edges, the natural
choice of `R` is a multiple of the adjacency matrix, and the bound is asymptotically sharp:
on the Paley graph it returns `ϑ = √p`.  For a graph that is only *approximately* strongly
regular — the Paley 1-localization `G_{p,1}` is the case this problem is about — the bound
degrades gracefully in the size of the deviation, which is what makes it a route to the
`√(p/2)` of Randomstrasse101 Problem 26 that the ratio bound provably cannot reach.

## Term-by-term read-back

* `V`, `Fintype V`, `DecidableEq V`, `Nonempty V` — a nonempty finite vertex type.
* `adj` — the adjacency relation, hypothesised symmetric (`∀ u v, adj u v → adj v u`) and
  irreflexive (`∀ u, ¬ adj u u`).  Nothing else about `adj` is assumed; in particular it is
  not assumed decidable and no `SimpleGraph` structure is imposed.
* `A` — the 0/1 adjacency matrix, pinned by `∀ u v, adj u v → A u v = 1` together with
  `∀ u v, ¬ adj u v → A u v = 0`.  These two hypotheses determine `A` completely.
* `m = (Fintype.card V : ℝ)` — the number of vertices, as a real.
* `∀ u, ∑ v, A u v = d` — `d`-regularity.  Every row of `A` sums to `d`.
* `R` — the *deviation matrix*.  Its diagonal vanishes (`∀ u, R u u = 0`) and on every edge
  it records how far the common-neighbour count departs from its average:
  `∀ u v, adj u v → R u v = (A * A) u v - d ^ 2 / m`, and `(A * A) u v = |N(u) ∩ N(v)|`.
  **Off the edges `R` is entirely free.**  That freedom is the content: the bound is a
  minimum over all completions of the edge data, and a good completion is what buys a
  constant better than the ratio bound's.
* `(c • 1 - R).PosSemidef` — `c` dominates the largest eigenvalue of `R`.
* the conclusion — `Commons.thetaClique adj`, the `ϑ` of the complement of `adj`, i.e. the
  semidefinite upper bound on the *clique* number, is at most
  `(m / (m - d)) * (1 + √(d - d² / m + c))`.

## What this does and does not say

It is a ceiling, not a value: it bounds `thetaClique` above and asserts nothing below.  It is
not vacuous — for any regular graph one may take `R` to be the deviation on edges and `0`
elsewhere and `c` its largest eigenvalue, and the hypotheses are then all satisfied.  It does
not assume strong regularity, vertex-transitivity, or any arithmetic structure, so it applies
to `Commons.paleyLocAdj p` exactly as it applies to any other regular graph.
-/

namespace Statements.ThetaCliqueSecondMoment

/-- The canonical proposition.  A second-moment ceiling on `ϑ` of the complement of a
`d`-regular graph, controlled by one eigenvalue bound `c` on the deviation of the
common-neighbour counts from their average `d² / m`. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (adj : V → V → Prop) (A R : Matrix V V ℝ) (m d c : ℝ),
    m = (Fintype.card V : ℝ) →
    (∀ u v, adj u v → adj v u) →
    (∀ u, ¬ adj u u) →
    (∀ u v, adj u v → A u v = 1) →
    (∀ u v, ¬ adj u v → A u v = 0) →
    (∀ u, ∑ v, A u v = d) →
    (∀ u, R u u = 0) →
    (∀ u v, adj u v → R u v = (A * A) u v - d ^ 2 / m) →
    (c • (1 : Matrix V V ℝ) - R).PosSemidef →
    Commons.thetaClique adj ≤ (m / (m - d)) * (1 + Real.sqrt (d - d ^ 2 / m + c))

/-- The open target. -/
theorem target : statement := sorry

end Statements.ThetaCliqueSecondMoment
