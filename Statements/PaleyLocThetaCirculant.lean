import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocThetaCirculant — the Lovász program for `G_{p,1}` may be solved over circulants

The semidefinite program defining `Commons.paleyLocTheta p` ranges over `((p-1)/2)²` real
parameters.  Every treatment of this problem in practice replaces it by a **linear** program
in `(p-1)/2` parameters, on the grounds that `G_{p,1}` is circulant.  The step that licences
that replacement is this one: any feasible point of the semidefinite program can be replaced,
without changing its objective value, by one that is invariant under the multiplicative action
of the nonzero squares — i.e. by a matrix of the form `Y u v = g(u·v⁻¹)`.

That is a genuine reduction of the search space and it is the half of "the SDP is an LP" that
does not need Fourier analysis: averaging a feasible `X` over the group,
`Y := |Q|⁻¹ ∑_{w ∈ Q} X(w·−, w·−)`, preserves positive semidefiniteness (each summand is a
submatrix of `X` along an injection), the trace (each `w·−` is a bijection), the zero pattern
(the action preserves adjacency), and the objective (likewise).  The remaining half — that a
circulant is positive semidefinite exactly when its Fourier coefficients are nonnegative — is
not claimed here.

Consequently a search for certificates may be restricted to circulants with no loss, and the
numerical values of `ϑ(Ḡ_{p,1})` obtained from the Delsarte linear program are lower bounds
on the semidefinite optimum for a reason that is checkable rather than folkloric.
-/

namespace Statements.PaleyLocThetaCirculant

/-- The canonical proposition: every feasible point of the Lovász program for the Paley
1-localization can be replaced by a circulant one with the same objective. -/
abbrev statement : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
    haveI : NeZero p := NeZero.of_pos hp.pos
    ∀ X : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ,
      X.PosSemidef → X.trace = 1 →
      (∀ u v : Commons.PaleyLocV p, u ≠ v → ¬ Commons.paleyLocAdj p u v → X u v = 0) →
      ∃ Y : Matrix (Commons.PaleyLocV p) (Commons.PaleyLocV p) ℝ,
        Y.PosSemidef ∧ Y.trace = 1 ∧
        (∀ u v : Commons.PaleyLocV p, u ≠ v → ¬ Commons.paleyLocAdj p u v → Y u v = 0) ∧
        (∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, Y u v)
          = (∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v) ∧
        ∃ g : ZMod p → ℝ, ∀ u v : Commons.PaleyLocV p,
          Y u v = g ((u : ZMod p) * (v : ZMod p)⁻¹)

theorem target : statement := sorry

end Statements.PaleyLocThetaCirculant
