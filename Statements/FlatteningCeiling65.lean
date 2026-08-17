import Mathlib

/-!
# The flattening ceiling at the first open case `(k,t) = (6,5)`

O'Neill–Verstraëte (arXiv:2011.09402v1, Definition 2 and equation (2)) reduce
`b_{k,t}` to a modulo-2 hypergraph cover number,
`f_{k,t}(n) = f'_k(H_{k,t}(n)) = min {m : b_{k,t}(m) ≥ n}`, where `H_{k,t}(n)` is the
`k`-partite `k`-graph on `X₁ × ⋯ × X_k` whose edges are the tuples with at least `t`
distinct indices.  A complete `k`-partite `k`-graph is exactly a rank-one `0/1` tensor, so
`f_{k,t}(n)` is the `F₂` tensor rank of the indicator `T` below; Conjecture 1 at `(6,5)` is
the assertion `f_{6,5}(n) = Ω(n³)`.

Every flattening of a tensor gives a matrix-rank lower bound on its tensor rank, and that is
the mechanism behind the paper's own Lemma 4 and Lemma 6.  This statement measures how far
that mechanism can possibly reach at `(6,5)`: **not past `7n²`**, a factor `n` short of the
`Ω(n³)` the conjecture needs.

The cause is exact and algebraic.  Off the degenerate strata the balanced `3|3` flattening
is `W_n[A,B] = [|A ∩ B| ≤ 1]` on `3`-subsets, and over `F₂`, `C(j,2) ≡ [j ≥ 2]` for `j ≤ 3`,
so `W_n = J + Mᵀ M` where `M` is the `2`-subset/`3`-subset inclusion matrix.  Every rank
bound is therefore forced through a space of dimension `C(n,2)`.

The matrix here is presented on the square index set `(Fin 6 → Fin n)`: the `(a,b)` entry
reads the `S`-coordinates from `a` and the remaining coordinates from `b`.  Rows agreeing on
`S` are equal and columns agreeing on `Sᶜ` are equal, so its rank is exactly the rank of the
genuine `n^{|S|} × n^{6-|S|}` flattening — no `Finset`-indexed matrix type is needed and every
`S ⊆ Fin 6` is covered by one quantifier, including the trivial shapes.

Scope discipline, which the statement itself cannot carry: this bounds **flattenings**.  It
says nothing about substitution, laser, slice/partition rank, or any non-flattening method,
and nothing about the true value of `rank_{F₂}(T)`, which is untested at every `n ≥ 5`.
-/

namespace Statements.FlatteningCeiling65

open Finset

/-- The `(6,5)` tensor over `F₂` on ground set `Fin n`: the entry at `i` is `1` exactly when
at least five of the six indices `i₀, …, i₅` are distinct.  This is the indicator of
`H_{6,5}(n)`. -/
def T (n : ℕ) (i : Fin 6 → Fin n) : ZMod 2 :=
  if 5 ≤ (image i univ).card then 1 else 0

/-- The `S`-flattening of `T`, on the square index set `(Fin 6 → Fin n)`. -/
def flat (n : ℕ) (S : Finset (Fin 6)) :
    Matrix (Fin 6 → Fin n) (Fin 6 → Fin n) (ZMod 2) :=
  fun a b => T n (fun j => if j ∈ S then a j else b j)

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (S : Finset (Fin 6)), (flat n S).rank ≤ 7 * n ^ 2

/-- The target. -/
theorem target : statement := sorry

end Statements.FlatteningCeiling65
