import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Commons.PaleyLocalizationTheta

namespace Submissions.PaleyLocThetaCirculant.GroupAverage

open Matrix Commons

variable {p : ℕ} [Fact (Nat.Prime p)]

lemma sq_mul {s t : ZMod p} (hs : IsNonzeroSq s) (ht : IsNonzeroSq t) :
    IsNonzeroSq (s * t) := by
  obtain ⟨hs0, a, rfl⟩ := hs
  obtain ⟨ht0, b, rfl⟩ := ht
  exact ⟨mul_ne_zero hs0 ht0, a * b, by ring⟩

lemma sq_inv {s : ZMod p} (hs : IsNonzeroSq s) : IsNonzeroSq s⁻¹ := by
  obtain ⟨hs0, a, rfl⟩ := hs
  have ha : a ≠ 0 := by intro h; exact hs0 (by rw [h]; ring)
  exact ⟨inv_ne_zero hs0, a⁻¹, by field_simp⟩

variable [NeZero p]

/-- the multiplicative action of a vertex on a vertex -/
def act (w u : PaleyLocV p) : PaleyLocV p := ⟨(w : ZMod p) * (u : ZMod p), sq_mul w.2 u.2⟩

def vinv (w : PaleyLocV p) : PaleyLocV p := ⟨((w : ZMod p))⁻¹, sq_inv w.2⟩

@[simp] lemma act_coe (w u : PaleyLocV p) : ((act w u : PaleyLocV p) : ZMod p)
    = (w : ZMod p) * (u : ZMod p) := rfl

@[simp] lemma vinv_coe (w : PaleyLocV p) : ((vinv w : PaleyLocV p) : ZMod p)
    = ((w : ZMod p))⁻¹ := rfl

/-- the action of a fixed `w` is a permutation of the vertex set -/
def actEquiv (w : PaleyLocV p) : PaleyLocV p ≃ PaleyLocV p where
  toFun := act w
  invFun := act (vinv w)
  left_inv u := by
    apply Subtype.ext
    have hw : (w : ZMod p) ≠ 0 := w.2.1
    simp [act, vinv]
    field_simp
  right_inv u := by
    apply Subtype.ext
    have hw : (w : ZMod p) ≠ 0 := w.2.1
    simp [act, vinv]
    field_simp

lemma act_injective (w : PaleyLocV p) : Function.Injective (act w) :=
  (actEquiv w).injective

lemma act_adj (w u v : PaleyLocV p) :
    paleyLocAdj p (act w u) (act w v) ↔ paleyLocAdj p u v := by
  have hw : (w : ZMod p) ≠ 0 := w.2.1
  constructor
  · intro h
    have he : ((act w u : PaleyLocV p) : ZMod p) - ((act w v : PaleyLocV p) : ZMod p)
        = (w : ZMod p) * ((u : ZMod p) - (v : ZMod p)) := by simp [act]; ring
    have h2 : IsNonzeroSq ((w : ZMod p) * ((u : ZMod p) - (v : ZMod p))) := by rwa [← he]
    have h3 := sq_mul (sq_inv w.2) h2
    have h4 : ((w : ZMod p))⁻¹ * ((w : ZMod p) * ((u : ZMod p) - (v : ZMod p))) = (u : ZMod p) - (v : ZMod p) := by
      field_simp
    rwa [h4] at h3
  · intro h
    have he : ((act w u : PaleyLocV p) : ZMod p) - ((act w v : PaleyLocV p) : ZMod p)
        = (w : ZMod p) * ((u : ZMod p) - (v : ZMod p)) := by simp [act]; ring
    show IsNonzeroSq _
    rw [he]
    exact sq_mul w.2 h


theorem proof :
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
            Y u v = g ((u : ZMod p) * (v : ZMod p)⁻¹) := by
  intro p hp hp4
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := NeZero.of_pos hp.pos
  intro X hX htr hzero
  classical
  have hone : Commons.IsNonzeroSq (1 : ZMod p) := ⟨one_ne_zero, ⟨1, by ring⟩⟩
  haveI : Nonempty (Commons.PaleyLocV p) := ⟨⟨1, hone⟩⟩
  set N : ℕ := Fintype.card (Commons.PaleyLocV p) with hNdef
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨((N:ℝ))⁻¹ • ∑ w : Commons.PaleyLocV p, X.submatrix (act w) (act w), ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.smul
      (Matrix.posSemidef_sum _ (fun w _ => Matrix.PosSemidef.submatrix hX (act w)))
      (by positivity)
  all_goals
    have hYval : ∀ u v : Commons.PaleyLocV p,
        (((N:ℝ))⁻¹ • ∑ w : Commons.PaleyLocV p, X.submatrix (act w) (act w)) u v
          = ((N:ℝ))⁻¹ * ∑ w : Commons.PaleyLocV p, X (act w u) (act w v) := by
      intro u v
      simp [Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  · -- trace
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl fun u _ => hYval u u, ← Finset.mul_sum, Finset.sum_comm]
    have hin : ∀ w : Commons.PaleyLocV p,
        ∑ u : Commons.PaleyLocV p, X (act w u) (act w u) = (1:ℝ) := by
      intro w
      rw [← htr]
      rw [Matrix.trace]
      simp only [Matrix.diag_apply]
      exact Fintype.sum_equiv (actEquiv w) _ _ (fun u => rfl)
    rw [Finset.sum_congr rfl fun w _ => hin w, Finset.sum_const, Finset.card_univ, ← hNdef,
      nsmul_eq_mul, mul_one]
    field_simp
  · -- zero pattern
    intro u v huv hadj
    rw [hYval u v]
    have : ∀ w : Commons.PaleyLocV p, X (act w u) (act w v) = 0 := by
      intro w
      refine hzero _ _ (fun hc => huv (act_injective w hc)) ?_
      rw [act_adj w u v]
      exact hadj
    rw [Finset.sum_congr rfl fun w _ => this w]
    simp
  · -- objective
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hYval u v]
    have hrow : ∀ u : Commons.PaleyLocV p,
        ∑ v : Commons.PaleyLocV p, ((N:ℝ))⁻¹ * ∑ w : Commons.PaleyLocV p, X (act w u) (act w v)
          = ((N:ℝ))⁻¹ * ∑ w : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p,
              X (act w u) (act w v) := by
      intro u; rw [← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u _ => hrow u, ← Finset.mul_sum, Finset.sum_comm]
    have hin : ∀ w : Commons.PaleyLocV p,
        ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X (act w u) (act w v)
          = ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p, X u v := by
      intro w
      refine Fintype.sum_equiv (actEquiv w) _ _ (fun u => ?_)
      exact Fintype.sum_equiv (actEquiv w) _ _ (fun v => rfl)
    rw [Finset.sum_congr rfl fun w _ => hin w, Finset.sum_const, Finset.card_univ, ← hNdef,
      nsmul_eq_mul]
    field_simp
  · -- circulant
    refine ⟨fun x => if h : Commons.IsNonzeroSq x then
      ((N:ℝ))⁻¹ * ∑ w : Commons.PaleyLocV p, X (act w ⟨x, h⟩) w else 0, ?_⟩
    intro u v
    rw [hYval u v]
    have ht : Commons.IsNonzeroSq ((u : ZMod p) * ((v : ZMod p))⁻¹) :=
      sq_mul u.2 (sq_inv v.2)
    dsimp only
    rw [dif_pos ht]
    congr 1
    refine Fintype.sum_equiv (actEquiv v) _ _ (fun w => ?_)
    have hv : (v : ZMod p) ≠ 0 := v.2.1
    have e1 : act ((actEquiv v) w) ⟨(u : ZMod p) * ((v : ZMod p))⁻¹, ht⟩ = act w u := by
      apply Subtype.ext
      show (v : ZMod p) * (w : ZMod p) * ((u : ZMod p) * ((v : ZMod p))⁻¹)
        = (w : ZMod p) * (u : ZMod p)
      field_simp
    have e2 : ((actEquiv v) w : Commons.PaleyLocV p) = act w v := by
      apply Subtype.ext
      show (v : ZMod p) * (w : ZMod p) = (w : ZMod p) * (v : ZMod p)
      ring
    rw [e1, e2]

end Submissions.PaleyLocThetaCirculant.GroupAverage
