import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

namespace Submissions.PaleyLocSelfDualReduction.SelfDualSqueeze

open Commons

noncomputable def coTheta (p : ℕ) (hp : 0 < p) : ℝ :=
  haveI : NeZero p := NeZero.of_pos hp
  Commons.thetaClique (fun u v : Commons.PaleyLocV p => u ≠ v ∧ ¬ Commons.paleyLocAdj p u v)

section General
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem feasible_nonneg (adj : V → V → Prop) {s : ℝ}
    (hs : s ∈ thetaCliqueFeasible adj) : 0 ≤ s := by
  obtain ⟨X, hX, -, -, rfl⟩ := hs
  have h := hX.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have e : (fun _ => (1:ℝ)) ⬝ᵥ X.mulVec (fun _ => 1) = ∑ u, ∑ v, X u v := by
    simp [dotProduct, Matrix.mulVec]
  simpa [e] using h

theorem thetaClique_nonneg (adj : V → V → Prop) : 0 ≤ thetaClique adj :=
  Real.sSup_nonneg (fun _ hx => feasible_nonneg adj hx)

end General

theorem coTheta_nonneg (p : ℕ) (hp : 0 < p) : 0 ≤ coTheta p hp := by
  haveI : NeZero p := NeZero.of_pos hp
  exact thetaClique_nonneg _

theorem paleyLocTheta_nonneg (p : ℕ) (hp : 0 < p) : 0 ≤ Commons.paleyLocTheta p hp := by
  haveI : NeZero p := NeZero.of_pos hp
  exact thetaClique_nonneg _

theorem proof :
    (∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
        Commons.paleyLocTheta p hp.pos * coTheta p hp.pos = ((p : ℝ) - 1) / 2) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → N < p →
        Commons.paleyLocTheta p hp.pos ≤ (1 + ε) * Real.sqrt ((p : ℝ) / 2) ∧
          coTheta p hp.pos ≤ (1 + ε) * Real.sqrt ((p : ℝ) / 2)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 → N < p →
        |Commons.paleyLocTheta p hp.pos / Real.sqrt ((p : ℝ) / 2) - 1| < ε) := by
  intro hprod hub ε hε
  obtain ⟨N₁, hN₁⟩ := hub (ε/3) (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (3/ε)
  refine ⟨max N₁ (max M 5), ?_⟩
  intro p hp hp4 hpN
  have hpN1 : N₁ < p := lt_of_le_of_lt (le_max_left _ _) hpN
  have hpM : M < p := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hpN
  have hp5 : 5 < p := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hpN
  obtain ⟨ha, hb⟩ := hN₁ p hp hp4 hpN1
  have hab := hprod p hp hp4
  have ha0 : 0 ≤ Commons.paleyLocTheta p hp.pos := paleyLocTheta_nonneg p hp.pos
  have hb0 : 0 ≤ coTheta p hp.pos := coTheta_nonneg p hp.pos
  set a := Commons.paleyLocTheta p hp.pos
  set b := coTheta p hp.pos
  set R := Real.sqrt ((p : ℝ) / 2) with hRdef
  have hp5' : (5:ℝ) < (p:ℝ) := by exact_mod_cast hp5
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hR0 : 0 < R := Real.sqrt_pos.mpr (by linarith)
  have hR2 : R * R = (p:ℝ)/2 := Real.mul_self_sqrt (by linarith)
  have hep : 3 < ε * (p:ℝ) := by
    have h1 : (3/ε) < (p:ℝ) := lt_trans hM (by exact_mod_cast hpM)
    have := (div_lt_iff₀ hε).mp h1
    linarith
  -- the ratio
  have hAR : (a / R) * R = a := div_mul_cancel₀ a (ne_of_gt hR0)
  set A := a / R with hAdef
  have hA0 : 0 ≤ A := div_nonneg ha0 (le_of_lt hR0)
  -- upper bound on A
  have hAhi : A < 1 + ε := by
    have : A ≤ 1 + ε/3 := by
      rw [hAdef, div_le_iff₀ hR0]; linarith
    linarith
  -- lower bound on A
  have key : (p:ℝ) - 1 ≤ A * (1 + ε/3) * (p:ℝ) := by
    have h2 : ((p:ℝ) - 1)/2 ≤ a * ((1 + ε/3) * R) := by
      calc ((p:ℝ) - 1)/2 = a * b := hab.symm
        _ ≤ a * ((1 + ε/3) * R) := mul_le_mul_of_nonneg_left hb ha0
    have haA : a = A * R := hAR.symm
    have h3 : a * ((1 + ε/3) * R) = A * (1 + ε/3) * ((p:ℝ)/2) := by
      rw [haA, ← hR2]; ring
    rw [h3] at h2; linarith
  have hAlo : 1 - ε < A := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon, key, hep, hε, hp0, hA0]
  rw [abs_lt]
  constructor <;> linarith

end Submissions.PaleyLocSelfDualReduction.SelfDualSqueeze
