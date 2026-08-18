import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
# Coordinate slices of an empty polytope of an exponential lattice
-/

set_option maxHeartbeats 1000000

namespace Submissions.ExpLatticeSliceReduction.SliceProof

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ₀}^d ⊆ ℝ^d`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `V` is the vertex set of a convex polytope that is empty in `S`. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- Forget the last coordinate. -/
def pr (x : Fin 3 → ℝ) : Fin 2 → ℝ := ![x 0, x 1]

theorem pr_linear : IsLinearMap ℝ pr := by
  constructor
  · intro x y
    funext i
    fin_cases i <;> simp [pr]
  · intro c x
    funext i
    fin_cases i <;> simp [pr]

theorem convex_level (c : ℝ) : Convex ℝ {x : Fin 3 → ℝ | x 2 = c} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx, hy]
  rw [← add_mul, hst, one_mul]

theorem fibre {α : ℝ} {V : Set (Fin 3 → ℝ)} (hV : IsEmptyPolytope (expLattice 3 α) V)
    (c : ℝ) : IsEmptyPolytope (expLattice 2 α) (pr '' {v | v ∈ V ∧ v 2 = c}) := by
  obtain ⟨hfin, hsub, hcp, hemp⟩ := hV
  set F : Set (Fin 3 → ℝ) := {v | v ∈ V ∧ v 2 = c} with hFdef
  have hFV : F ⊆ V := fun v hv => hv.1
  have hFc : ∀ v ∈ F, v 2 = c := fun v hv => hv.2
  have hhull : convexHull ℝ F ⊆ {x : Fin 3 → ℝ | x 2 = c} :=
    convexHull_min (fun v hv => hFc v hv) (convex_level c)
  refine ⟨(hfin.subset hFV).image pr, ?_, ?_, ?_⟩
  · rintro w ⟨v, hv, rfl⟩ i
    fin_cases i
    · obtain ⟨n, hn⟩ := hsub (hFV hv) 0
      refine ⟨n, ?_⟩
      show pr v 0 = α ^ n
      simpa [pr] using hn
    · obtain ⟨n, hn⟩ := hsub (hFV hv) 1
      refine ⟨n, ?_⟩
      show pr v 1 = α ^ n
      simpa [pr] using hn
  · rintro w ⟨v, hv, rfl⟩ hmem
    have hstep : (pr '' F) \ {pr v} ⊆ pr '' (F \ {v}) := by
      rintro y ⟨⟨u, hu, rfl⟩, hne⟩
      refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      rintro rfl
      exact hne rfl
    have h1 : pr v ∈ convexHull ℝ (pr '' (F \ {v})) := convexHull_mono hstep hmem
    rw [← pr_linear.image_convexHull] at h1
    obtain ⟨w, hw, hwv⟩ := h1
    have hw2 : w 2 = c := hhull (convexHull_mono Set.diff_subset hw)
    have hwveq : w = v := by
      funext i
      fin_cases i
      · have h0 := congrFun hwv 0
        simpa [pr] using h0
      · have h1' := congrFun hwv 1
        simpa [pr] using h1'
      · show w 2 = v 2
        rw [hw2, hFc v hv]
    rw [hwveq] at hw
    have hsub2 : F \ {v} ⊆ V \ {v} := fun u hu => ⟨hFV hu.1, hu.2⟩
    exact hcp v (hFV hv) (convexHull_mono hsub2 hw)
  · rintro p ⟨hp, hpS⟩
    rw [← pr_linear.image_convexHull] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hq2 : q 2 = c := hhull hq
    have hFne : F.Nonempty := convexHull_nonempty_iff.mp ⟨q, hq⟩
    obtain ⟨v0, hv0⟩ := hFne
    obtain ⟨n2, hn2⟩ := hsub (hFV hv0) 2
    have hc : c = α ^ n2 := by rw [← hFc v0 hv0]; exact hn2
    have hqlat : q ∈ expLattice 3 α := by
      intro i
      fin_cases i
      · obtain ⟨n, hn⟩ := hpS 0
        refine ⟨n, ?_⟩
        show q 0 = α ^ n
        simpa [pr] using hn
      · obtain ⟨n, hn⟩ := hpS 1
        refine ⟨n, ?_⟩
        show q 1 = α ^ n
        simpa [pr] using hn
      · refine ⟨n2, ?_⟩
        show q 2 = α ^ n2
        rw [hq2, hc]
    have hqV : q ∈ V := hemp ⟨convexHull_mono hFV hq, hqlat⟩
    exact ⟨q, ⟨hqV, hq2⟩, rfl⟩

theorem count {α : ℝ} {V : Set (Fin 3 → ℝ)} (hV : IsEmptyPolytope (expLattice 3 α) V)
    (N : ℕ) (hN : ∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N) :
    V.ncard ≤ N * ((fun v : Fin 3 → ℝ => v 2) '' V).ncard := by
  classical
  have hfin : V.Finite := hV.1
  set s : Finset (Fin 3 → ℝ) := hfin.toFinset with hs
  have hcoe : (↑s : Set (Fin 3 → ℝ)) = V := hfin.coe_toFinset
  have key : ∀ b ∈ s.image (fun v : Fin 3 → ℝ => v 2),
      (s.filter (fun v : Fin 3 → ℝ => v 2 = b)).card ≤ N := by
    intro b _
    have hinj : Set.InjOn pr {v : Fin 3 → ℝ | v ∈ V ∧ v 2 = b} := by
      intro x hx y hy hxy
      funext i
      fin_cases i
      · show x 0 = y 0
        simpa [pr] using congrFun hxy 0
      · show x 1 = y 1
        simpa [pr] using congrFun hxy 1
      · show x 2 = y 2
        rw [hx.2, hy.2]
    have h1 : (pr '' {v : Fin 3 → ℝ | v ∈ V ∧ v 2 = b}).ncard ≤ N := hN _ (fibre hV b)
    have h2 : ({v : Fin 3 → ℝ | v ∈ V ∧ v 2 = b}).ncard ≤ N := by
      rwa [hinj.ncard_image] at h1
    have h3 : (↑(s.filter (fun v : Fin 3 → ℝ => v 2 = b)) : Set (Fin 3 → ℝ))
        = {v : Fin 3 → ℝ | v ∈ V ∧ v 2 = b} := by
      ext x
      simp [hs, Set.Finite.mem_toFinset]
    rw [← Set.ncard_coe_finset, h3]
    exact h2
  have hb := Finset.card_le_mul_card_image s N key
  have e1 : V.ncard = s.card := by rw [← hcoe, Set.ncard_coe_finset]
  have e2 : ((fun v : Fin 3 → ℝ => v 2) '' V).ncard
      = (s.image (fun v : Fin 3 → ℝ => v 2)).card := by
    rw [← hcoe, ← Finset.coe_image, Set.ncard_coe_finset]
  rw [e1, e2]
  exact hb

/-- **The slice reduction.**  Every coordinate fibre of an empty polytope of `L₃(α)`
projects to an empty polytope of `L₂(α)`; consequently, if the planar Helly number is at
most `N`, then an empty polytope of `L₃(α)` has at most `N` times as many vertices as it
has distinct third coordinates. -/
theorem proof :
    ∀ (α : ℝ) (V : Set (Fin 3 → ℝ)), IsEmptyPolytope (expLattice 3 α) V →
      (∀ c : ℝ, IsEmptyPolytope (expLattice 2 α) (pr '' {v | v ∈ V ∧ v 2 = c})) ∧
      ∀ N : ℕ, (∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N) →
        V.ncard ≤ N * ((fun v : Fin 3 → ℝ => v 2) '' V).ncard :=
  fun _ _ hV => ⟨fun c => fibre hV c, fun N hN => count hV N hN⟩


end Submissions.ExpLatticeSliceReduction.SliceProof
