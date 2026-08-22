import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Even

/-!
# QubitUniformAnsatzFourDividesM — corrected qubit rigidity (supersedes UniformAnsatzQubitFourDividesM)

**Per-state form, false:** every orthogonal product family with a 2-regular qubit
orthogonality class has `4 ∣ m`. Counterexample: `jig.so/p/6` / `MinUPB227`, size 10.

**Uniform ansatz, surviving claim:** when the qubit class is a uniform 2-factor —
disjoint union of qubit-repetition cycles (`x,y,x,y,…`, each of length divisible by 4) —
one has `4 ∣ m`.

Supersedes `UniformAnsatzQubitFourDividesM`, whose canonical file imported a nonexistent
module and could not build.
-/

namespace Statements.QubitUniformAnsatzFourDividesM

abbrev QubitRepetitionCycle (c : ℕ) : Prop := Even c ∧ 4 ∣ c

abbrev statement : Prop :=
  ∀ cycles : List ℕ,
    (∀ c ∈ cycles, QubitRepetitionCycle c) →
    4 ∣ cycles.foldl (· + ·) 0

theorem target : statement := sorry

end Statements.QubitUniformAnsatzFourDividesM
