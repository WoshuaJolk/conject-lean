import Mathlib

namespace Submissions.TorusNonvanishing.Torus

open Complex ComplexConjugate

noncomputable section

def circlePoint (x : ℝ) : Circle :=
  Circle.ofConjDivSelf (x + I) (by
    intro h
    have hi := congrArg im h
    simpa using hi)

lemma circlePoint_injective : Function.Injective circlePoint := by
  intro x y h
  have h' :
      conj ((x : ℂ) + I) / ((x : ℂ) + I) =
        conj ((y : ℂ) + I) / ((y : ℂ) + I) := by
    exact congrArg (fun z : Circle => (z : ℂ)) h
  have hx : (x : ℂ) + I ≠ 0 := by
    intro h
    have hi := congrArg im h
    simpa using hi
  have hy : (y : ℂ) + I ≠ 0 := by
    intro h
    have hi := congrArg im h
    simpa using hi
  field_simp [hx, hy] at h'
  have hxs :
      (starRingEnd ℂ) ((x : ℂ) + I) = (x : ℂ) - I := by
    rw [← Complex.star_def]
    simp [sub_eq_add_neg]
  have hys :
      (starRingEnd ℂ) ((y : ℂ) + I) = (y : ℂ) - I := by
    rw [← Complex.star_def]
    simp [sub_eq_add_neg]
  rw [hxs, hys] at h'
  have hxy : (2 : ℂ) * I * ((x : ℂ) - y) = 0 := by
    linear_combination h'
  have hxy' : (x : ℂ) - y = 0 := by
    rcases mul_eq_zero.mp hxy with h0 | h0
    · norm_num at h0
    · exact h0
  exact_mod_cast sub_eq_zero.mp hxy'

lemma unitCircle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  let g : ℝ → ℂ := fun x => (circlePoint x : ℂ)
  have hg : Function.Injective g := by
    intro x y hxy
    apply circlePoint_injective
    exact Circle.ext hxy
  refine Set.infinite_of_injective_forall_mem
    (s := {z : ℂ | ‖z‖ = 1}) hg ?_
  intro x
  simpa [g] using Circle.norm_coe (circlePoint x)

lemma nonvanishing_on_torus {k : ℕ} {p : MvPolynomial (Fin k) ℂ}
    (hp : p ≠ 0) :
    ∃ z : Fin k → ℂ,
      (∀ r, ‖z r‖ = 1) ∧ MvPolynomial.eval z p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext_set
    (fun _ : Fin k => {z : ℂ | ‖z‖ = 1})
    (fun _ => unitCircle_infinite)
  intro z hz
  have hnorm : ∀ r, ‖z r‖ = 1 := fun r => hz r (Set.mem_univ _)
  simpa using h z hnorm

lemma simultaneous_nonvanishing {k N : ℕ}
    (p : Fin N → MvPolynomial (Fin k) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ z : Fin k → ℂ,
      (∀ r, ‖z r‖ = 1) ∧
        ∀ i, MvPolynomial.eval z (p i) ≠ 0 := by
  let q : MvPolynomial (Fin k) ℂ := ∏ i : Fin N, p i
  have hq : q ≠ 0 := by
    dsimp [q]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact hp i)
  obtain ⟨z, hz, hqz⟩ := nonvanishing_on_torus hq
  refine ⟨z, hz, ?_⟩
  have hprod :
      (∏ i : Fin N, MvPolynomial.eval z (p i)) ≠ 0 := by
    simpa [q, map_prod] using hqz
  intro i
  exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

theorem target : ∀ (k N : ℕ)
    (p : Fin N → MvPolynomial (Fin k) ℂ), (∀ i, p i ≠ 0) →
      ∃ z : Fin k → ℂ,
        (∀ r, ‖z r‖ = 1) ∧
          ∀ i, MvPolynomial.eval z (p i) ≠ 0 := by
  intro k N p hp
  exact simultaneous_nonvanishing p hp

end

end Submissions.TorusNonvanishing.Torus
