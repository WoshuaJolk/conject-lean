import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# GadgetComplementOneFactorization — the other factors always have room

Context. The classification route at `m = f_N + 1` needs `E(K_m)` split into one degenerate
`k`-regular class and non-degenerate `(d_j - 1)`-regular classes. Once the degenerate class is
*fixed* — and it must be, since general position is impossible for a `k`-regular class in dimension
`k`, so that class cannot come from Lovász–Saks–Schrijver and has to be an explicit gadget — the
remaining classes no longer decompose `K_m`. They decompose `K_m` minus the gadget graph. That is a
genuine extra requirement, and this statement is the first half of it: the complement is
1-factorizable at all. (The second half, that some *grouping* of those factors satisfies the LSS
connectivity condition per class, is separate and is not claimed here.)

The gadget graph. The degenerate seed is two orthonormal bases of `ℂ^k` matched up: its orthogonality
graph `G_k` is two disjoint `K_k`s plus a perfect matching between them, on `2k` vertices, and it is
`k`-regular. Sizes add by the copies core, so the degenerate class on `m = 2kc` vertices is `c`
disjoint copies of `G_k`. Vertices are therefore indexed by `Fin c × Fin 2 × Fin k`: a copy, a side,
and a position, with `G_k` joining equal `(copy, side)` pairs and matching equal `(copy, position)`
pairs.

The graph to factorize. Deleting `G` from `K_m` leaves exactly: all edges between distinct copies,
and inside a copy, the pairs with *different* side and *different* position. Inside one copy that is
`K_{k,k}` minus a perfect matching, which is `(k-1)`-regular; between copies it is the complete
multipartite graph with `c` parts of size `2k`, which is `2k(c-1)`-regular. So the graph is
`(m - 1 - k)`-regular, since `(k - 1) + 2k(c - 1) = 2kc - k - 1`.

Why it should be provable rather than searched. Both halves are classical and neither needs a search,
which is the point of filing this: earlier attempts to find these factorizations by exact CP-SAT
timed out at `k = 4` in the one-copy case, and that case is König's theorem.

* Inside a copy, `K_{k,k}` minus the perfect matching `{(i, i)}` is 1-factorized *explicitly* by
  `(i, j) ↦ (j - i) mod k`, whose classes `{(i, i + d)}` for `d = 1, …, k-1` are perfect matchings.
  Matching the per-copy factors up index-wise turns them into `k - 1` perfect matchings of all `m`
  vertices.
* Between copies, Laskar–Auerbach decompose the complete equipartite graph `K(n; c)` into
  `n(c-1)/2` Hamiltonian cycles whenever `n(c-1)` is even, which holds here since `n = 2k` is even;
  each Hamiltonian cycle on an even number of vertices splits into two perfect matchings, giving
  `2k(c-1)` factors. Both halves therefore hold for every `k ≥ 2` and every `c ≥ 1`, with no parity
  case distinction.

Formalization. A 1-factorization is encoded as an indexed family of involutions `F t` with `F t v`
always a neighbour of `v` — so each `F t` is a perfect matching — such that every edge lies in
exactly one factor.
-/

namespace Statements.GadgetComplementOneFactorization

/-- Vertices of `m = 2kc` vectors: a copy of the gadget, a side (which of its two bases), and a
position within that basis. -/
abbrev V (c k : ℕ) : Type := Fin c × Fin 2 × Fin k

/-- `K_m` minus the degenerate class: all edges between distinct copies, and inside a copy exactly
the pairs with different side and different position — that is, `K_{k,k}` minus a perfect matching. -/
def compl (c k : ℕ) : SimpleGraph (V c k) :=
  SimpleGraph.fromRel fun v w =>
    v.1 ≠ w.1 ∨ (v.1 = w.1 ∧ v.2.1 ≠ w.2.1 ∧ v.2.2 ≠ w.2.2)

/-- The canonical proposition: for every `k ≥ 2` and `c ≥ 1`, the complement of `c` disjoint copies
of the gadget graph in `K_{2kc}` has a 1-factorization into its `2kc - k - 1` factors — given as
involutions `F t`, each pairing every vertex with a neighbour, with every edge in exactly one. -/
abbrev statement : Prop :=
  ∀ k c : ℕ, 2 ≤ k → 1 ≤ c →
    ∃ F : Fin (2 * k * c - k - 1) → V c k → V c k,
      (∀ t v, (compl c k).Adj v (F t v)) ∧
      (∀ t v, F t (F t v) = v) ∧
      (∀ v w, (compl c k).Adj v w → ∃! t, F t v = w)

theorem target : statement := sorry

end Statements.GadgetComplementOneFactorization
