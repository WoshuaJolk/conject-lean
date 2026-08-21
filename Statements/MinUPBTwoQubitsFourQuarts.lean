import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MinUPBTwoQubitsFourQuarts — the root of p/14 at dimensions `(2,2,4,4,4,4)`

This is `MinUPBAtMostTrivialPlusOne` instantiated at two qubits and four four-dimensional
factors: it asserts an unextendible product basis of size at most `f_N + 1 = 16` in
`C^2 ⊗ C^2 ⊗ (C^4)^{⊗4}`, where `f_N = 1 + 1 + 1 + 4·3 = 15`.

The tuple is open in the literature. `f_N = 15` is odd and not every local dimension is odd, so
Alon–Lovász's parity criterion gives `f_m ≥ f_N + 1 = 16` and rules out the trivial value.
Chen–Johnston's Theorem 1 needs one factor to dominate (`d_p − 1 ≥ Σ_{j<p} (d_j − 1)`, here
`3 ≥ 12`, false), the system is neither bipartite nor all-qubit, and `(2,2,4^4)` is not among the
tuples listed as known in Chen–Johnston §2. So a witness of size 16 settles a case no published
result reaches, and by the parity lower bound settles it optimally.

## Why this tuple, and not just this tuple

It is the base case of an infinite family, and the first instance where the construction needs no
search at all. The two green engines on this board fix the shape of any size-`(f_N + 1)` witness:
`GenPosUPBTrivialCeiling` (`jig.so/p/14?s=2`) says a family in general position in every factor
cannot exceed `f_N`, so exactly one factor must be degenerate, and `UPBFromDegreeBudget`
(`jig.so/p/14?s=3`) reduces unextendibility to `Σ_j c_j < m` for per-factor killing numbers.
Here the budget is `2 + 1 + 4·3 = 15 < 16`, which forces the six orthogonality graphs to
partition `E(K_16)` with degrees `2, 1, 3, 3, 3, 3`.

Two mechanisms then supply every piece.

*The degenerate factor is a qubit, as in `MinUPB224kMinus1` (`jig.so/p/6`).* Two orthogonal
directions, each used twice, give killing number `2` and a `K_{2,2}` orthogonality graph, so a
degenerate qubit factor's graph is a disjoint union of 4-cycles. Putting a second, ordinary qubit
factor's perfect matching on the diagonals of those 4-cycles makes the two qubit factors together
cover exactly a `K_4`-factor: `4 + 2 = 6` edges per block.

*The general-position factors come from the moment curve.* For `γ(s) = (1, s, s², s³)` in `C^4`
the Hermitian pairing is `Σ_{k<4} (conj s · t)^k = ((conj s · t)^4 − 1)/(conj s · t − 1)`, so with
`s = η^a`, `t = η^b` for `η` a primitive 16th root of unity, `γ(η^a) ⟂ γ(η^b)` exactly when
`a ≠ b` and `a ≡ b (mod 4)`. Distinct exponents make every four of the vectors a Vandermonde
matrix, hence independent: general position, and killing number `3`, for free. Sixteen exponents
split into four residue classes mod 4 therefore realize a disjoint-`K_4`-factor explicitly.

So the construction reduces to a design: partition `K_16` minus a `K_4`-factor into four
parallel classes of `K_4`s. That is a resolvable transversal design `RTD(4,4)`, equivalently
three MOLS of order 4, equivalently the line classes of `AG(2,4)` — take the 16 points of
`GF(4)²`, one parallel class of lines as the `K_4`-factor carrying the two qubits, and the other
four as the four `C^4` factors. Counting is exact: `4·6 + 16·6 = 120 = C(16,2)`.

The moment curve is how the general-position factors are obtained uniformly in the dimension, but
at a fixed size any realization of the same disjoint-`K_4` graph will do, and integer orthogonal
frames in `Z^4` — four mutually orthogonal quadruples per factor, no four of the sixteen vectors
in a hyperplane — realize it with rational certificates instead of cyclotomic ones.

The same recipe with `K_{4n}` minus a `K_4`-factor is a `(4,1)`-RGDD of type `4^n`, which exists
for every `n ≥ 4` with `n ≡ 1 (mod 3)` and no exceptions (Sun–Ge, Discrete Math. 309 (2009)
2982–2989, Thm 2.1), giving `f_m(2,2,4^t) = 3t + 4` for every `t ≡ 0 (mod 4)`. This statement is
the case `n = 4`, where the design is classical and the whole witness is explicit.

## Reading the formalisation

The proposition is the root's conclusion at `p = 6` and `d = (2,2,4,4,4,4)`, verbatim and in the
same order, so a proof of this is literally a case of `MinUPBAtMostTrivialPlusOne`: the
existential size `m`, the bound `m ≤ 2 + Σ_j (d j − 1)`, nonzero local vectors, pairwise
orthogonality in some factor, and unextendibility against every product vector with all local
components nonzero, `∃ i` innermost.

`dims` is a plain comparison on the factor index rather than a list literal, so that
`Fin (dims j)` is reducible and the bound `2 + Σ_j (dims j − 1) = 16` is a `decide`-level fact.
-/

namespace Statements.MinUPBTwoQubitsFourQuarts

/-- Two qubits and four four-dimensional factors. -/
abbrev dims : Fin 6 → ℕ := fun j => if j.val < 2 then 2 else 4

abbrev statement : Prop :=
  ∃ m : ℕ, m ≤ 2 + ∑ j, (dims j - 1) ∧
    ∃ v : Fin m → (j : Fin 6) → Fin (dims j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin 6) → Fin (dims j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MinUPBTwoQubitsFourQuarts
