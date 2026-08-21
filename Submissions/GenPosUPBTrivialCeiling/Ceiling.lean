import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace Submissions.GenPosUPBTrivialCeiling.Ceiling

set_option maxRecDepth 40000
set_option maxHeartbeats 10000000

open Finset

def ip {d : ℕ} (x y : Fin d → ℂ) : ℂ := ∑ r, star (x r) * y r

lemma ip_self_ne_zero {d : ℕ} {x : Fin d → ℂ} (hx : x ≠ 0) : ip x x ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r, x r ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have key : ∀ r : Fin d, star (x r) * x r = ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have h := RCLike.conj_mul (K := ℂ) (x r)
    push_cast
    simpa using h
  have hsum : ip x x = ((∑ r, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  rw [hsum]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => sq_nonneg ‖x r‖)).1 hzero
  have hn : ‖x r₀‖ = 0 := by
    have h2 := hall r₀ (Finset.mem_univ r₀)
    nlinarith [norm_nonneg (x r₀)]
  exact hr₀ (norm_eq_zero.1 hn)

lemma annihilates_of_linearIndependent {d : ℕ} {x : Fin d → ℂ}
    {b : Fin d → (Fin d → ℂ)}
    (hb : LinearIndependent ℂ b)
    (horth : ∀ t, ip x (b t) = 0) : x = 0 := by
  have hspan : Submodule.span ℂ (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank' (Module.finrank_fintype_fun_eq_card ℂ).symm
  let φ : (Fin d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun y => ip x y
      map_add' := by
        intro y z
        simp [ip, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp [ip, Finset.mul_sum, mul_left_comm] }
  have hφ : φ = 0 := by
    apply LinearMap.ext_on_range hspan
    intro t
    simpa [φ] using horth t
  have hxx : ip x x = 0 := by
    have := congrArg (fun f => f x) hφ
    simpa [φ] using this
  exact (by_contra fun hne => ip_self_ne_zero hne hxx)

theorem proof :
    ∀ p m : ℕ, ∀ d : Fin p → ℕ, ∀ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
      (∀ i j, v i j ≠ 0) →
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) →
      (∀ j, (∀ f : Fin (d j) → Fin m, Function.Injective f →
        LinearIndependent ℂ (fun t : Fin (d j) => v (f t) j))) →
      m ≤ 1 + ∑ j, (d j - 1) := by
  intro p m d v hnonzero horth hgen
  by_cases hm0 : m = 0
  · omega
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  let i₀ : Fin m := ⟨0, hmpos⟩
  let A : Fin p → Finset (Fin m) := fun j =>
    Finset.univ.filter (fun i => i ≠ i₀ ∧ ip (v i₀ j) (v i j) = 0)
  have hdpos : ∀ j, 0 < d j := by
    intro j
    by_contra hj
    have hdj : d j = 0 := by omega
    have hz : v i₀ j = 0 := by
      funext r
      exact Fin.elim0 (hdj ▸ r)
    exact hnonzero i₀ j hz
  have hcover : Finset.univ.erase i₀ ⊆ Finset.univ.biUnion A := by
    intro i hi
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    obtain ⟨j, hj⟩ := horth i₀ i (Ne.symm hne)
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne, hj⟩
  have hcover_card : m - 1 ≤ ∑ j, (A j).card := by
    calc
      m - 1 = (Finset.univ.erase i₀).card := by simp
      _ ≤ (Finset.univ.biUnion A).card := Finset.card_le_card hcover
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin p)), (A j).card :=
        Finset.card_biUnion_le
      _ = ∑ j, (A j).card := by simp
  have hAcap : ∀ j, (A j).card + 1 ≤ d j := by
    intro j
    by_contra hbad
    have hdle : d j ≤ (A j).card := by omega
    obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hdle
    let e : Fin (d j) ≃o S := S.orderIsoOfFin hScard
    let f : Fin (d j) → Fin m := fun t => e t
    have hf : Function.Injective f := by
      intro a b hab
      apply e.injective
      exact Subtype.ext hab
    have hli := hgen j f hf
    have hspan : Submodule.span ℂ
        (Set.range (fun t : Fin (d j) => v (f t) j)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank'
        (Module.finrank_fintype_fun_eq_card ℂ).symm
    let φ : (Fin (d j) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun y => ip (v i₀ j) y
        map_add' := by
          intro y z
          simp [ip, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro a y
          simp [ip, Finset.mul_sum, mul_left_comm] }
    have hφ : φ = 0 := by
      apply LinearMap.ext_on_range hspan
      intro t
      have hmem : f t ∈ A j := hSA (e t).property
      have hz : ip (v i₀ j) (v (f t) j) = 0 :=
        (Finset.mem_filter.mp hmem).2.2
      simpa [φ] using hz
    have hself : ip (v i₀ j) (v i₀ j) = 0 := by
      have := congrArg (fun g => g (v i₀ j)) hφ
      simpa [φ] using this
    exact (ip_self_ne_zero (hnonzero i₀ j)) hself
  have hsum : ∑ j, ((A j).card + 1) ≤ ∑ j, d j := by
    exact Finset.sum_le_sum (fun j _ => hAcap j)
  have harith : m ≤ 1 + ∑ j, (d j - 1) := by
    have hsum' : ∑ j, (A j).card + p ≤ ∑ j, d j := by
      simpa [Finset.sum_add_distrib] using hsum
    have hsub : ∀ j, 1 ≤ d j := by
      intro j
      exact hdpos j
    have hsum_sub : ∑ j, (d j - 1) + p = ∑ j, d j := by
      calc
        ∑ j, (d j - 1) + p = ∑ j, ((d j - 1) + 1) := by
          simp [Finset.sum_add_distrib]
        _ = ∑ j, d j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Nat.sub_add_cancel (hsub j)
    have hcardA : m - 1 ≤ ∑ j, (A j).card := hcover_card
    omega
  exact harith

end Submissions.GenPosUPBTrivialCeiling.Ceiling
