import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# VandermondeCliqueRows — an all-dimensions family with a forced graph and free general position

Convention (as in `CopiesTransversalCore`, `PhasePlacementUniform`, `MinorSplitPhaseTransversal`,
`UniformSecondBlockPlacement`, and opposite to Lovász–Saks–Schrijver): an edge of the orthogonality
graph means the two vectors *are* orthogonal.

Context. Every witness so far has been found by search in a fixed dimension: a graph is chosen, then
vectors realizing it are hunted for, then tightness and spanning are checked by exhaustive exact
sweeps. That gives seeds in the dimensions one happens to look at. This statement supplies instead a
*uniform* family, one construction valid in every dimension `k`, whose orthogonality graph is forced
by an identity rather than verified, and whose general position is free.

The construction. Attach to a node `s : ℂ` the Vandermonde row `vand s = (1, s, s², …, s^(k-1))`.
Two rows pair as a geometric sum: with `ρ = conj s * s'`,

    pair (vand s) (vand s') = ∑_{r < k} ρ ^ r,

so the two rows are orthogonal exactly when `ρ ^ k = 1` and `ρ ≠ 1`. Adjacency is therefore a
statement about the ratio of the two nodes and nothing else, which is what makes the graph
computable rather than searched: choosing nodes among the `N`-th roots of unity with `N = k * M`
splits them into cosets of the subgroup of order `k`, each coset a clique `K k` and distinct cosets
joined by no edge at all, giving a disjoint union of `K k`'s — a `(k-1)`-regular graph — in every
dimension. Note the hypothesis is only that the nodes are *distinct*; unit modulus is not needed for
either clause, so the identity is available for the non-unimodular nodes too.

General position is free. Any `k` distinct nodes give a genuine Vandermonde matrix, so its
determinant is the product of the node differences and is nonzero: every selection of `k` distinct
nodes is linearly independent. Tightness in the sense used throughout (every subset of size at most
`k - 1` independent) and `(k+1)`-spanning are then both immediate, and are recorded here as the
second and third clauses since they are the inputs the killing-number bound and the copies core
consume.

Scope. This is the family for the *non-degenerate* classes, of degree `k - 1` in dimension `k`. It
cannot supply the degenerate `k`-regular class, and that is not a search failure: adjacency forces
`‖s‖ * ‖s'‖ = 1`, so two adjacent nodes inside one clique force unit modulus, hence all nodes lie on
the circle, hence adjacency means the ratio lies in the group of `k`-th roots of unity — and a coset
of that group has exactly `k` elements, so a node has at most `k - 1` neighbours. Nothing is claimed
here about phases, placements, or unextendibility; nothing is claimed for `k = 1`.
-/

namespace Statements.VandermondeCliqueRows

variable {k : ℕ}

/-- The Hermitian pairing on `Fin k → ℂ`, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The Vandermonde row attached to a node: `(1, s, s², …, s^(k-1))`. -/
abbrev vand (k : ℕ) (s : ℂ) : Fin k → ℂ := fun r => s ^ (r : ℕ)

/-- The canonical proposition.

For `k ≥ 2` and any family of *distinct* nodes:

* orthogonality of two Vandermonde rows is exactly the condition that the ratio `conj s * s'` is a
  `k`-th root of unity other than `1`;
* every selection of `k` distinct nodes gives linearly independent rows;
* every selection of `k + 1` distinct nodes spans `Fin k → ℂ`.

The first clause forces the orthogonality graph, the second gives tightness (subsets of size at most
`k - 1` are subsets of independent sets), the third gives `(k+1)`-spanning. -/
abbrev statement : Prop :=
  ∀ (k n : ℕ), 2 ≤ k →
    ∀ t : Fin n → ℂ, Function.Injective t →
      (∀ i j : Fin n,
          pair (vand k (t i)) (vand k (t j)) = 0 ↔
            ((star (t i) * t j) ^ k = 1 ∧ star (t i) * t j ≠ 1)) ∧
      (∀ b : Fin k → Fin n, Function.Injective b →
          LinearIndependent ℂ fun p => vand k (t (b p))) ∧
      (∀ b : Fin (k + 1) → Fin n, Function.Injective b →
          Submodule.span ℂ (Set.range fun p => vand k (t (b p))) = ⊤)

theorem target : statement := sorry

end Statements.VandermondeCliqueRows
