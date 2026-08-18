import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# ThetaCliqueCertificates — the two-sided certificate calculus for `Commons.thetaClique`

`Commons.thetaClique adj` is defined as an `sSup` of a set of reals, and an `sSup` in Mathlib
is only as good as the two facts nobody gets for free: that the set is bounded above (else it
is the junk value `0`), and that a given element is in it.  Every attempt on this problem —
either half of Randomstrasse Conjecture 26 — has to supply exactly one of two objects:

* an **upper certificate**: a symmetric `A` that is `1` on the diagonal and on the edges, with
  `t • 1 - A` positive semidefinite.  This is the dual of the Lovász program, and it caps `ϑ`
  at `t` by weak duality: `∑ᵤᵥ Xᵤᵥ = ⟨A, X⟩` for every feasible `X`, because `A` and the
  all-ones matrix agree wherever `X` may be nonzero, and `⟨t·1 - A, X⟩ ≥ 0` because the
  Frobenius pairing of two positive semidefinite matrices is nonnegative.

* a **lower certificate**: a single feasible `X`.  Its objective is a lower bound *provided*
  the supremum is not junk, which is precisely what an upper certificate supplies.

The statement packages both, over an arbitrary finite vertex type and an arbitrary relation:
from one upper certificate at level `t` you get `ϑ ≤ t` **and** the licence to read every
feasible point as a lower bound.  It is graph-theoretic, not Paley-specific, and it is the
tool `PaleyLocThetaWindow` is an instance of; the bridge to this problem is that
`Commons.paleyLocTheta p = Commons.thetaClique (Commons.paleyLocAdj p)` by definition, so
every certificate for the Paley 1-localization is an instance of this statement.

`0 ≤ t` is a hypothesis rather than a consequence because on an empty vertex type the feasible
set is empty and `sSup ∅ = 0`.
-/

namespace Statements.ThetaCliqueCertificates

/-- The canonical proposition: an upper certificate caps `thetaClique`, and licences every
feasible point as a lower bound. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (adj : V → V → Prop)
    (A : Matrix V V ℝ) (t : ℝ), 0 ≤ t →
    (∀ u, A u u = 1) → (∀ u v, adj u v → A u v = 1) →
    (t • (1 : Matrix V V ℝ) - A).PosSemidef →
    Commons.thetaClique adj ≤ t ∧
      ∀ X : Matrix V V ℝ, X.PosSemidef → X.trace = 1 →
        (∀ u v, u ≠ v → ¬ adj u v → X u v = 0) →
        (∑ u, ∑ v, X u v) ≤ Commons.thetaClique adj

theorem target : statement := sorry

end Statements.ThetaCliqueCertificates
