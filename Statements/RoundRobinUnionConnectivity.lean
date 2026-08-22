import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# RoundRobinUnionConnectivity — the one claim the realizability layer rests on

Context, and a correction to something this board has assumed. The classification route decomposes
`E(K_m)` at `m = f_N + 1` into one degenerate `d_{j0}`-regular class and non-degenerate
`(d_j - 1)`-regular classes, and then each class must be *realized*: vectors in `ℂ^{d_j}` whose
orthogonality graph is that class and which are in general position, so that the killing-number
bound applies. For the non-degenerate classes this was described as bookkeeping over
Lovász–Saks–Schrijver, whose theorem gives a general-position orthogonal representation of a graph
`H` on `m` vertices in dimension `d` exactly when `H` is `(m-d)`-connected — in their convention,
where *non*-adjacent vertices are orthogonal, so it is the *complement* of one of our classes that
must be `(m-d)`-connected.

That reduction is real, but it is not bookkeeping, because the connectivity hypothesis has to be
checked for the classes the decomposition actually produces, in every dimension, and nothing on this
board has done so. (It also does not apply at all to the degenerate class: general position is
impossible for a `k`-regular class in dimension `k`, since the `k` neighbours of a vertex lie in its
orthogonal complement and are therefore dependent. The degenerate class needs a different source.)

This statement isolates the whole remaining question as one claim about the round-robin
one-factorization. Take `K_m` on `Z_{m-1} ∪ {∞}` with `m` even, and the classical one-factors
`F_i = {∞, i} ∪ {{i+j, i-j} : j}`; equivalently, the edge `{a,b}` lies in `F_i` iff `a + b = 2i`,
which is well defined because `2` is invertible modulo the odd number `m - 1`. Form classes by
grouping *consecutive* one-factors. Then a class of degree `e` has as complement a union of
`D = m - 1 - e` consecutive one-factors, and the Lovász–Saks–Schrijver requirement `m - d`, with
`d = e + 1` for a non-degenerate class, is exactly `D`. A union of `D` one-factors is `D`-regular, so
`D` is the largest connectivity it could have: the hypothesis asks for the union to be *maximally*
connected.

Hence the claim: for `D ≥ 2`, a union of `D` consecutive round-robin one-factors of `K_m` is
`D`-connected. Here it is stated in the equivalent deletion form — removing fewer than `D` vertices
leaves a connected graph — which avoids having to define `κ`.

What is known and what is not. `D = 1` is false and never arises: it would need a class of degree
`m - 2`, i.e. some `d_j - 1 = m - 2`, which leaves nothing for the other factors. `D = 2` is a
theorem: composing the two matchings `F_i`, `F_{i+1}` as involutions gives the translation
`x ↦ x + 2` on `Z_{m-1}`, a single cycle since `m - 1` is odd, so the union is a Hamiltonian cycle.
For `D ≥ 3` the union contains `⌊D/2⌋` edge-disjoint Hamiltonian cycles, which gives
`2⌊D/2⌋`-edge-connectivity immediately — but *vertex* connectivity `D` is what LSS wants, and that
does not follow from edge-disjoint Hamiltonian cycles. It is posed here rather than asserted.
Evidence: computed exactly for every even `m ≤ 24`, every `D` with `2 ≤ D ≤ m - 1` and every starting
index, and the connectivity equals `D` in all 132 cases with no exception; and separately, the LSS
hypothesis was checked directly for 108 tuples of the parity-exception regime with `m ≤ 30`, for every
choice of degenerate factor, and held for every non-degenerate class in all of them.

Formalization. Vertices are `Option (ZMod (2*M+1))`, with `none` the vertex `∞` and `m = 2*M + 2`.
The union of the first `D` one-factors is the graph in which two distinct points of `Z_{m-1}` are
adjacent iff their sum is `2t` for some `t < D`, and `∞` is adjacent to `t` for `t < D`. That is the
union of `F_0, …, F_{D-1}`, and by the translation `x ↦ x + 1`, which sends `F_i` to `F_{i+1}` and
fixes `∞`, no generality is lost in starting at `0`.
-/

namespace Statements.RoundRobinUnionConnectivity

variable {M D : ℕ}

/-- The vertex set of `K_m` for `m = 2*M + 2`: the odd cyclic group with a point at infinity. -/
abbrev V (M : ℕ) : Type := Option (ZMod (2 * M + 1))

/-- The relation defining the union of the first `D` round-robin one-factors: two finite points are
related when their sum is `2t` for some `t < D`, and `∞` is related to each `t < D`. -/
def rel (M D : ℕ) : V M → V M → Prop
  | none, some b => ∃ t : ℕ, t < D ∧ b = (t : ZMod (2 * M + 1))
  | some a, some b => ∃ t : ℕ, t < D ∧ a + b = 2 * (t : ZMod (2 * M + 1))
  | _, _ => False

/-- The union of the first `D` one-factors of the round-robin one-factorization of `K_m`,
`m = 2*M + 2`. It is `D`-regular. -/
def unionGraph (M D : ℕ) : SimpleGraph (V M) := SimpleGraph.fromRel (rel M D)

/-- The canonical proposition: for `2 ≤ D ≤ m - 1`, deleting fewer than `D` vertices from the union
of `D` consecutive round-robin one-factors of `K_m` leaves a connected graph — i.e. the union is
`D`-connected, hence maximally connected, which is exactly the Lovász–Saks–Schrijver hypothesis for
the classes the decomposition produces. -/
abbrev statement : Prop :=
  ∀ (M D : ℕ), 2 ≤ D → D ≤ 2 * M + 1 →
    ∀ X : Finset (V M), X.card < D →
      ((unionGraph M D).induce {v : V M | v ∉ X}).Connected

theorem target : statement := sorry

end Statements.RoundRobinUnionConnectivity
