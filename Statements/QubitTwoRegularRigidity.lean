import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# QubitTwoRegularRigidity — an exactly 2-regular qubit orthogonality graph forces `4 ∣ m`

The degenerate-factor supply problem at local dimension 2, settled negatively for
`m ≢ 0 (mod 4)`: if `m` nonzero vectors in `C^2` have Hermitian orthogonality graph exactly
2-regular — every vector has exactly two orthogonal partners — then `4 ∣ m` (the graph is
forced to be a disjoint union of 4-cycles).

**Proof shape.** In `C^2` the orthogonal complement of a nonzero vector is a single complex
line, so a vector's two orthogonal partners are parallel to each other. Parallelism classes
therefore have exactly two members (a third would give some partner three orthogonal
partners), each class's common orthogonal set is exactly one opposite class, and the pairing
of classes is fixed-point-free (a vector is never orthogonal to a parallel one — they would
be orthogonal and proportional, hence zero). So the vertex set splits into disjoint
`K_{2,2}`'s — 4-cycles — and `4 ∣ m`.

**Scope discipline, and the neighbouring false claim.** The hypothesis is exact 2-regularity
of the *intrinsic* orthogonality graph, not "killing number 2": the killing-number reading —
a degenerate qubit factor (some functional annihilating two states) forces `4 ∣ m` — is
FALSE, witnessed at `m = 10` by the `(2,2,7)` basis of `MinUPB227` (jig.so/p/6), whose qubit
factor has parallel classes of sizes `2,2,2,2,1,1` and hence two vertices of orthogonality
degree 1, escaping the hypothesis here. `QubitUniformAnsatzFourDividesM` (this board) proves
the combinatorial uniform-ansatz version; this statement is the intrinsic geometric version.

**Why it matters for the classification.** Together with the killing-budget accounting, it
pins the budget-shaped witnesses: when every per-factor degree is forced (killing numbers
summing to `m − 1`), a degenerate qubit factor's graph is exactly 2-regular, so budget-shaped
witnesses with a qubit exceptional factor exist only when `4 ∣ m`. This is why the
`(2,2,4^t)` family lives at `t ≡ 0 (mod 4)` and why the `m ≡ 2 (mod 4)` tuples
`(2,2,4,4)` and `(2,3,3,4)` had to route through the `k = 4` gadget (`MinUPB2244`,
`MinUPB2334`).

**Reading the formalisation.** Exact 2-regularity is stated existentially, with no Finset or
decidability apparatus: every vertex has two distinct orthogonal partners, and any orthogonal
partner is one of the two. The inner product is the standard Hermitian one, conjugate-linear
in the first slot.
-/

namespace Statements.QubitTwoRegularRigidity

abbrev statement : Prop :=
  ∀ m : ℕ, ∀ v : Fin m → Fin 2 → ℂ,
    (∀ i, v i ≠ 0) →
    (∀ i : Fin m, ∃ j k : Fin m,
      j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (∑ r, star (v i r) * v j r) = 0 ∧
      (∑ r, star (v i r) * v k r) = 0 ∧
      (∀ l : Fin m, l ≠ i → (∑ r, star (v i r) * v l r) = 0 → (l = j ∨ l = k))) →
    4 ∣ m

theorem target : statement := sorry

end Statements.QubitTwoRegularRigidity
