import Mathlib

/-!
# The scaling barrier for empty polytopes of exponential lattices

For any nonempty set `S` of coordinates, the diagonal map multiplying the coordinates in
`S` by `α` sends `L₃(α)` into itself and preserves convex hulls.  This module shows that
the orbit of any point under that map meets an empty polytope of `L₃(α)` in at most two
points, at consecutive exponents.  Hence no scale-invariant construction can produce empty
polytopes of unbounded size from boundedly many directions.
-/

namespace Submissions.ExpLatticeScalingBarrier.Scal

def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- Scale the coordinates selected by `s` by `α ^ d`. -/
def scal (α : ℝ) (s : Fin 3 → Bool) (d : ℕ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (if s i then α ^ d else 1) * u i

theorem key {α : ℝ} (hα : 1 < α) {V : Set (Fin 3 → ℝ)}
    (hV : IsEmptyPolytope (expLattice 3 α) V)
    (u : Fin 3 → ℝ) (s : Fin 3 → Bool) (d : ℕ) (hd : 2 ≤ d) (i₀ : Fin 3) (hi₀ : s i₀ = true)
    (hu : u ∈ V) (hv : scal α s d u ∈ V) : False := by
  obtain ⟨-, hsub, hpos, hemp⟩ := hV
  have hα0 : (0:ℝ) < α := lt_trans zero_lt_one hα
  have hupos : ∀ i, 0 < u i := by
    intro i
    obtain ⟨k, hk⟩ := hsub hu i
    rw [hk]; exact pow_pos hα0 k
  have h1 : α ^ 1 < α ^ d := pow_lt_pow_right₀ hα (by omega)
  have hα1 : α ^ 1 = α := pow_one α
  have hgt : α < α ^ d := by rw [pow_one] at h1; exact h1
  have hden : (0:ℝ) < α ^ d - 1 := by linarith
  set t : ℝ := (α - 1) / (α ^ d - 1) with htdef
  have ht0 : 0 < t := div_pos (by linarith) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hsum : (1 - t) + t = 1 := by ring
  have hne : α ^ d - 1 ≠ 0 := ne_of_gt hden
  have htkey : 1 + t * (α ^ d - 1) = α := by
    have hcancel : (α - 1) / (α ^ d - 1) * (α ^ d - 1) = α - 1 :=
      div_mul_cancel₀ _ hne
    rw [htdef, hcancel]; ring
  set w : Fin 3 → ℝ := fun i => (if s i then α else 1) * u i with hwdef
  have hcomb : (1 - t) • u + t • scal α s d u = w := by
    funext i
    by_cases h : s i = true
    · simp only [hwdef, scal, h, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : (1 - t) * u i + t * (α ^ d * u i) = (1 + t * (α ^ d - 1)) * u i := by ring
      rw [e, htkey]
    · simp only [Bool.not_eq_true] at h
      simp only [hwdef, scal, h, Bool.false_eq_true, if_false, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, one_mul]
      ring
  have hwL : w ∈ expLattice 3 α := by
    intro i
    obtain ⟨k, hk⟩ := hsub hu i
    by_cases h : s i = true
    · refine ⟨k + 1, ?_⟩
      simp only [hwdef, h, if_true, hk, pow_succ]
      ring
    · simp only [Bool.not_eq_true] at h
      refine ⟨k, ?_⟩
      simp only [hwdef, h, Bool.false_eq_true, if_false, hk, one_mul]
  have hwhull : w ∈ convexHull ℝ V := by
    rw [← hcomb]
    exact (convex_convexHull ℝ V) (subset_convexHull ℝ V hu) (subset_convexHull ℝ V hv)
      (by linarith) (le_of_lt ht0) hsum
  have hwV : w ∈ V := hemp ⟨hwhull, hwL⟩
  have hwu : u ≠ w := by
    intro h
    have hc := congrFun h i₀
    simp only [hwdef, hi₀, if_true] at hc
    nlinarith [hupos i₀, hα]
  have hwv : scal α s d u ≠ w := by
    intro h
    have hc := congrFun h i₀
    simp only [hwdef, scal, hi₀, if_true] at hc
    nlinarith [hupos i₀, hgt]
  have hum : u ∈ V \ {w} := ⟨hu, fun h => hwu (Set.mem_singleton_iff.mp h)⟩
  have hvm : scal α s d u ∈ V \ {w} := ⟨hv, fun h => hwv (Set.mem_singleton_iff.mp h)⟩
  have hmem : (1 - t) • u + t • scal α s d u ∈ convexHull ℝ (V \ {w}) :=
    (convex_convexHull ℝ (V \ {w}))
      (subset_convexHull ℝ (V \ {w}) hum) (subset_convexHull ℝ (V \ {w}) hvm)
      (by linarith) (le_of_lt ht0) hsum
  rw [hcomb] at hmem
  exact hpos w hwV hmem


theorem scal_comp (α : ℝ) (s : Fin 3 → Bool) (a b : ℕ) (u : Fin 3 → ℝ) :
    scal α s a (scal α s b u) = scal α s (a + b) u := by
  funext i
  by_cases h : s i = true
  · simp only [scal, h, if_true, pow_add]
    ring
  · simp only [Bool.not_eq_true] at h
    simp only [scal, h, Bool.false_eq_true, if_false, one_mul]

theorem orbit_card {α : ℝ} (hα : 1 < α) {V : Set (Fin 3 → ℝ)}
    (hV : IsEmptyPolytope (expLattice 3 α) V) (u : Fin 3 → ℝ) (s : Fin 3 → Bool)
    (i₀ : Fin 3) (hi₀ : s i₀ = true) :
    {n : ℕ | scal α s n u ∈ V}.ncard ≤ 2 := by
  classical
  rcases Set.eq_empty_or_nonempty {n : ℕ | scal α s n u ∈ V} with h | h
  · rw [h]; simp
  · set k := sInf {n : ℕ | scal α s n u ∈ V} with hkdef
    have hk : scal α s k u ∈ V := Nat.sInf_mem h
    have hsub2 : {n : ℕ | scal α s n u ∈ V} ⊆ ({k, k + 1} : Set ℕ) := by
      intro n hn
      have h1 : k ≤ n := Nat.sInf_le hn
      have h2 : n ≤ k + 1 := by
        by_contra hc
        refine key hα hV (scal α s k u) s (n - k) (by omega) i₀ hi₀ hk ?_
        rw [scal_comp]
        have hnk : n - k + k = n := by omega
        rw [hnk]
        exact hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have hfin : ({k, k + 1} : Set ℕ).Finite := (Set.finite_singleton _).insert _
    calc {n : ℕ | scal α s n u ∈ V}.ncard
        ≤ ({k, k + 1} : Set ℕ).ncard := Set.ncard_le_ncard hsub2 hfin
      _ ≤ ({k + 1} : Set ℕ).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ 2 := by rw [Set.ncard_singleton]

theorem main : ∀ α : ℝ, 1 < α → ∀ V : Set (Fin 3 → ℝ),
    IsEmptyPolytope (expLattice 3 α) V →
    ∀ (u : Fin 3 → ℝ) (s : Fin 3 → Bool) (i₀ : Fin 3), s i₀ = true →
      {n : ℕ | (fun i => (if s i then α ^ n else 1) * u i) ∈ V}.ncard ≤ 2 ∧
      ∀ d : ℕ, 2 ≤ d → u ∈ V →
        (fun i => (if s i then α ^ d else 1) * u i) ∈ V → False := by
  intro α hα V hV u s i₀ hi₀
  exact ⟨orbit_card hα hV u s i₀ hi₀, fun d hd hu hv => key hα hV u s d hd i₀ hi₀ hu hv⟩


/-- **The statement.** -/
theorem proof :
    ∀ α : ℝ, 1 < α → ∀ V : Set (Fin 3 → ℝ),
      (V.Finite ∧ V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
        (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
        convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ V) →
      ∀ (u : Fin 3 → ℝ) (s : Fin 3 → Bool) (i₀ : Fin 3), s i₀ = true →
        {n : ℕ | (fun i => (if s i then α ^ n else 1) * u i) ∈ V}.ncard ≤ 2 ∧
        ∀ d : ℕ, 2 ≤ d → u ∈ V →
          (fun i => (if s i then α ^ d else 1) * u i) ∈ V → False :=
  main

end Submissions.ExpLatticeScalingBarrier.Scal
