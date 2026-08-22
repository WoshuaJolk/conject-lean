import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin

/-!
# RoundRobinRegularDecomposition — the combinatorial half of the budget-shaped witness

The classification of minimum unextendible product basis sizes at `f_N + 1` (this problem's
root) reduces, via `GenPosUPBTrivialCeiling` and `UPBFromDegreeBudget`, to two independent
supply problems: a spanning-regular edge decomposition of `K_m`, and vector realizations of its
classes. This statement is the decomposition half, in full generality, and it shows that layer
can never be the obstruction.

**Claim.** Let `m = L + 1` with `L` odd (every tuple in the exceptional regime has `f_N` odd,
so `m = f_N + 1` is even and `L = m - 1` is odd — the number of even local dimensions is even).
Then for every list of degrees `e_1, …, e_p` summing to `L = m − 1`, the edge set of `K_m`
partitions into `p` spanning subgraphs, the `j`-th regular of degree `e_j`. In particular, for
every exceptional tuple `(d_1..d_p)` and every choice of degenerate factor `j0`, the degree
pattern `e_{j0} = d_{j0}`, `e_j = d_j − 1` (`j ≠ j0`) is achievable: the degrees sum to
`f_N = m − 1`.

**Construction** (round-robin / Walecki). On vertices `Z_L ∪ {∞}`, the one-factors
`F_i = {∞, i} ∪ { {i+j, i−j} : j = 1..(L−1)/2 }`, `i ∈ Z_L`, partition `E(K_m)`: the edge
`{a, b} ⊆ Z_L` lies in `F_i` for the unique `i = (a+b)/2` (`2` is invertible mod the odd `L`),
and `{∞, a}` lies in `F_a`. Grouping the `F_i` into consecutive blocks of sizes `e_1, …, e_p`
gives the classes. Regularity at a finite vertex `v`: the map `u ↦ (u+v)/2` is a bijection of
`Z_L \ {v}` fixing nothing relevant, and the `∞`-edge tops up the count in `v`'s own block.

**Formalisation.** The decomposition is presented as a symmetric edge-colouring
`color : Fin (L+1) → Fin (L+1) → Fin p` (the diagonal is unconstrained and irrelevant), and
regularity as an exact fibre count at every vertex. Connectivity of the classes — true for
every class of degree ≥ 2 in the round-robin construction, since consecutive one-factor pairs
are Hamiltonian cycles — is deliberately not part of the canonical claim: the UPB application
consumes only the degrees.
-/

namespace Statements.RoundRobinRegularDecomposition

abbrev statement : Prop :=
  ∀ L : ℕ, Odd L →
    ∀ p : ℕ, ∀ e : Fin p → ℕ, (∑ j, e j) = L →
      ∃ color : Fin (L + 1) → Fin (L + 1) → Fin p,
        (∀ a b, color a b = color b a) ∧
        (∀ v : Fin (L + 1), ∀ j : Fin p,
          (Finset.univ.filter (fun u => u ≠ v ∧ color u v = j)).card = e j)

theorem target : statement := sorry

end Statements.RoundRobinRegularDecomposition
