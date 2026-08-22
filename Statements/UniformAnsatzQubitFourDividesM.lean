import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Parity

/-!
# UniformAnsatzQubitFourDividesM — corrected qubit rigidity

**Per-state form, false:** "every orthogonal product family with a 2-regular qubit
orthogonality class has `4 ∣ m`". Counterexample: `jig.so/p/6` / `MinUPB227`, size 10.

**Uniform ansatz, the surviving claim:** when the qubit class is a *uniform* 2-factor —
a disjoint union of even cycles coming from the same local repetition pattern
(`x,y,x,y,…` around each cycle) — each cycle has length divisible by 4, hence `4 ∣ m`.

This statement is that surviving combinatorial claim. It is not a claim about arbitrary
2-regular qubit classes, and it must not be used to prune mixed p/6-style patterns.
-/

namespace Statements.UniformAnsatzQubitFourDividesM

/-- A cycle length arising from the qubit repetition pattern is divisible by 4:
walking `x,y,x,y,…` around an even cycle closes only when the length is a multiple of 4. -/
abbrev QubitRepetitionCycle (c : ℕ) : Prop := Even c ∧ 4 ∣ c

/-- The canonical proposition.

If `m` is the sum of cycle lengths each of which is a qubit-repetition cycle
(even, and divisible by 4), then `4 ∣ m`. This is the uniform-ansatz rigidity lemma in
combinatorial form; the geometric embedding into `C^2` is left to the caller. -/
abbrev statement : Prop :=
  ∀ cycles : List ℕ,
    (∀ c ∈ cycles, QubitRepetitionCycle c) →
    4 ∣ cycles.foldl (· + ·) 0

theorem target : statement := sorry

end Statements.UniformAnsatzQubitFourDividesM
