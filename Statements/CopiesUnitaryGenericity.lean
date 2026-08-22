import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# CopiesUnitaryGenericity — the genericity half of the copies lemma

Companion to `CopiesTransversalCore` (jig.so/p/14?s=15). That statement takes
transversality and the absence of cross-orthogonality as hypotheses; this one
supplies them, by placing a second copy of a tight `(k+1)`-spanning family under
a unitary.

## Why not the diagonal torus

A tempting shortcut is to act by diagonal phases `diag(e^{iθ_r})`. That preserves
every *intra*-block pairing exactly, so the two blocks keep their graphs,
tightness and spanning for free, and the cross conditions become trigonometric
polynomials in the phases. The shortcut fails on the seeds we actually use: the
`C_10(1,2)` witness of `SpanningOrthRep4C10` has pairs with disjoint coordinate
support (e.g. `(1,0,0,0)` and `(0,0,0,2)`), for which
`∑_r v_i(r) v_j(r) e^{iθ_r}` is identically zero. So the phase torus is too
small; the bad set is the whole torus, not a proper subvariety.

## What this statement claims

The full unitary group is large enough. Given any finite family of nonzero
vectors that is tight and `(k+1)`-spanning, there exists a unitary matrix `U`
such that the two-block family `(v, U · v)` has

* no cross orthogonality, and
* the transversality property required by `CopiesTransversalCore`.

Together with that core, achievable gadget sizes are closed under addition, and
Chen–Johnston's consecutive sizes `2k−1, 2k` therefore generate every
sufficiently large size.

Convention: edge means orthogonal (opposite of Lovász–Saks–Schrijver). Hermitian
pairing conjugate-linear in the first slot.
-/

namespace Statements.CopiesUnitaryGenericity

open Matrix

variable {k : ℕ}

/-- Hermitian pairing, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

abbrev Tight {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card ≤ k - 1 → LinearIndependent ℂ fun i : (S : Set ι) => v i

abbrev Spanning {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i) = ⊤

abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) :
    Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

/-- A matrix is unitary when `U * star U = 1`. -/
abbrev IsUnitary (U : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  U * star U = 1

/-- Apply a `k × k` matrix to a coordinate vector. -/
abbrev applyMat (U : Matrix (Fin k) (Fin k) ℂ) (x : Fin k → ℂ) : Fin k → ℂ :=
  U.mulVec x

/-- The canonical proposition.

For every dimension `k ≥ 2` and every tight `(k+1)`-spanning family of nonzero
vectors in `C^k`, some unitary places a second copy so that the two blocks are
cross-nonorthogonal and transversal. (Intra-block geometry is automatic:
unitaries preserve all pairings.) -/
abbrev statement : Prop :=
  ∀ (k n : ℕ), 2 ≤ k →
    ∀ (v : Fin n → Fin k → ℂ),
      (∀ i, v i ≠ 0) → Tight v → Spanning v →
      ∃ U : Matrix (Fin k) (Fin k) ℂ,
        IsUnitary U ∧
        (∀ (i j : Fin n),
          pair (v i) (applyMat U (v j)) ≠ 0) ∧
        Transversal v (fun j => applyMat U (v j))

theorem target : statement := sorry

end Statements.CopiesUnitaryGenericity
