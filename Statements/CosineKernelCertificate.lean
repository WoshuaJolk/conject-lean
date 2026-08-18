import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# CosineKernelCertificate — turning nonnegative Fourier coefficients into a PSD certificate

`Statements.PaleyLocThetaCirculant` says the Lovász program for `G_{p,1}` may be solved over
circulants.  A circulant is normally certified positive semidefinite by saying "its Fourier
coefficients are nonnegative" — which is a theorem about characters of a cyclic group and is
not available in the pinned Mathlib.

It is not needed.  A circulant with nonnegative Fourier coefficients is, written out, a
nonnegative combination of **cosine kernels**, and a cosine kernel is a Gram matrix:

`cos(a - b) = cos a · cos b + sin a · sin b`,

so `u, v ↦ cos(φ u - φ v)` is `gᵀg + hᵀh` for `g = cos ∘ φ` and `h = sin ∘ φ`.  Hence the
statement below, which needs no Fourier theory at all, no cyclic group, and no characters:
**any nonnegative combination of cosine kernels is positive semidefinite.**

That is the whole of what a contributor needs in practice.  A numerically-obtained solution of
the Delsarte linear program for `G_{p,1}` arrives as a list of nonnegative coefficients
`c j` against phases `φ j u = 2π j·log(u)/|Q|`; feeding them here yields a positive
semidefinite matrix, `Statements.PaleyLocThetaCirculant` says nothing is lost by looking only
at such matrices, and `Statements.ThetaCliqueCertificates` turns the resulting feasible point
into a genuine lower bound on `ϑ`.  Together those three close the loop from a linear-program
solution to a kernel-checked bound.
-/

namespace Statements.CosineKernelCertificate

/-- The canonical proposition: a nonnegative combination of cosine kernels is positive
semidefinite. -/
abbrev statement : Prop :=
  ∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι]
    (c : ι → ℝ) (φ : ι → V → ℝ), (∀ j, 0 ≤ c j) →
    (Matrix.of fun u v : V => ∑ j : ι, c j * Real.cos (φ j u - φ j v)).PosSemidef

theorem target : statement := sorry

end Statements.CosineKernelCertificate
