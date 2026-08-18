import Mathlib

/-!
# The level reduction for empty polytopes of exponential lattices

Every level set of an empty polytope of `L₃(α)`, viewed in the plane by forgetting the
first coordinate, is an empty polytope of `L₂(α)`.  Hence a bound `N` on the planar Helly
number bounds `|V|` by `N` times the number of distinct first coordinates of `V`, and a
bound on the number of levels transfers planar finiteness to dimension three.
-/

namespace Submissions.ExpLatticeLevelReduction.Slice

def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- Put `r` into coordinate `0`. -/
def lift (r : ℝ) (y : Fin 2 → ℝ) : Fin 3 → ℝ := Fin.cons r y

/-- Forget coordinate `0`. -/
def tl (v : Fin 3 → ℝ) : Fin 2 → ℝ := fun i => v i.succ

@[simp] theorem lift_zero (r : ℝ) (y : Fin 2 → ℝ) : lift r y 0 = r := rfl

@[simp] theorem lift_succ (r : ℝ) (y : Fin 2 → ℝ) (i : Fin 2) : lift r y i.succ = y i := by
  simp [lift]

@[simp] theorem tl_lift (r : ℝ) (y : Fin 2 → ℝ) : tl (lift r y) = y := by
  funext i; simp [tl]

theorem lift_tl (v : Fin 3 → ℝ) : lift (v 0) (tl v) = v := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; simp [tl]

theorem lift_affine (r : ℝ) {y z : Fin 2 → ℝ} {a b : ℝ} (hab : a + b = 1) :
    lift r (a • y + b • z) = a • lift r y + b • lift r z := by
  funext i
  refine Fin.cases ?_ ?_ i
  · have : a * r + b * r = r := by
      rw [← add_mul, hab, one_mul]
    simpa using this.symm
  · intro j; simp

theorem convex_lift_preimage (r : ℝ) {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ (lift r ⁻¹' C) := by
  intro y hy z hz a b ha hb hab
  have : lift r (a • y + b • z) = a • lift r y + b • lift r z := lift_affine r hab
  simp only [Set.mem_preimage, this]
  exact hC hy hz ha hb hab

theorem lift_hull (r : ℝ) (T : Set (Fin 2 → ℝ)) :
    lift r '' (convexHull ℝ T) ⊆ convexHull ℝ (lift r '' T) := by
  rintro _ ⟨y, hy, rfl⟩
  have hsub : convexHull ℝ T ⊆ lift r ⁻¹' (convexHull ℝ (lift r '' T)) := by
    refine convexHull_min ?_ (convex_lift_preimage r (convex_convexHull ℝ _))
    intro t ht
    exact subset_convexHull ℝ _ ⟨t, ht, rfl⟩
  exact hsub hy

/-- The slice of `V` above the first coordinate `r`. -/
def slice (V : Set (Fin 3 → ℝ)) (r : ℝ) : Set (Fin 3 → ℝ) := {v | v ∈ V ∧ v 0 = r}

theorem lift_image_tl_slice (V : Set (Fin 3 → ℝ)) (r : ℝ) :
    lift r '' (tl '' slice V r) = slice V r := by
  ext v
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    have : lift r (tl u) = u := by rw [← hu.2]; exact lift_tl u
    rwa [this]
  · intro hv
    exact ⟨tl v, ⟨v, hv, rfl⟩, by rw [← hv.2]; exact lift_tl v⟩

/-- **The slice lemma.**  Every level set of an empty polytope of `L₃(α)`, viewed in the
plane by forgetting the first coordinate, is an empty polytope of `L₂(α)`. -/
theorem slice_isEmptyPolytope {α : ℝ} {V : Set (Fin 3 → ℝ)}
    (hV : IsEmptyPolytope (expLattice 3 α) V) (r : ℝ) :
    IsEmptyPolytope (expLattice 2 α) (tl '' slice V r) := by
  obtain ⟨hfin, hsub, hpos, hemp⟩ := hV
  have hslice_sub : slice V r ⊆ V := fun v hv => hv.1
  refine ⟨(hfin.subset hslice_sub).image tl, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ i
    obtain ⟨n, hn⟩ := hsub hv.1 i.succ
    exact ⟨n, hn⟩
  · rintro _ ⟨v, hv, rfl⟩ hmem
    have hlift : lift r (tl v) = v := by rw [← hv.2]; exact lift_tl v
    have h1 : v ∈ convexHull ℝ (lift r '' ((tl '' slice V r) \ {tl v})) := by
      have := lift_hull r ((tl '' slice V r) \ {tl v}) ⟨tl v, hmem, hlift⟩
      exact this
    refine hpos v hv.1 (convexHull_min ?_ (convex_convexHull ℝ _) h1)
    rintro _ ⟨y, ⟨⟨u, hu, rfl⟩, hne⟩, rfl⟩
    have hlu : lift r (tl u) = u := by rw [← hu.2]; exact lift_tl u
    refine subset_convexHull ℝ _ ⟨by rw [hlu]; exact hu.1, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hcontra
    have htt : tl u = tl v := by
      have h := congrArg tl hcontra
      rwa [tl_lift] at h
    exact hne (Set.mem_singleton_iff.mpr htt)
  · rintro y ⟨hy, hyL⟩
    rcases Set.eq_empty_or_nonempty (slice V r) with hE | ⟨v0, hv0⟩
    · rw [hE] at hy; simp at hy
    · have hr : ∃ n : ℕ, r = α ^ n := by
        obtain ⟨n, hn⟩ := hsub hv0.1 0
        exact ⟨n, by rw [← hv0.2]; exact hn⟩
      have h1 : lift r y ∈ convexHull ℝ (slice V r) := by
        rw [← lift_image_tl_slice V r]
        exact lift_hull r _ ⟨y, hy, rfl⟩
      have h2 : lift r y ∈ convexHull ℝ V :=
        convexHull_mono hslice_sub h1
      have h3 : lift r y ∈ expLattice 3 α := by
        intro i
        refine Fin.cases ?_ ?_ i
        · obtain ⟨n, hn⟩ := hr; exact ⟨n, by simpa using hn⟩
        · intro j; obtain ⟨n, hn⟩ := hyL j; exact ⟨n, by simpa using hn⟩
      have h4 : lift r y ∈ V := hemp ⟨h2, h3⟩
      exact ⟨lift r y, ⟨h4, rfl⟩, by simp⟩

theorem tl_injOn_slice (V : Set (Fin 3 → ℝ)) (r : ℝ) : Set.InjOn tl (slice V r) := by
  intro u hu w hw h
  have h1 : lift r (tl u) = u := by rw [← hu.2]; exact lift_tl u
  have h2 : lift r (tl w) = w := by rw [← hw.2]; exact lift_tl w
  rw [← h1, ← h2, h]


theorem slice_ncard_le {α : ℝ} {N : ℕ}
    (hN : ∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N)
    {V : Set (Fin 3 → ℝ)} (hV : IsEmptyPolytope (expLattice 3 α) V) (r : ℝ) :
    (slice V r).ncard ≤ N := by
  have h := hN _ (slice_isEmptyPolytope hV r)
  rwa [Set.InjOn.ncard_image (tl_injOn_slice V r)] at h

/-- **The level reduction.**  If every empty polytope of the planar exponential lattice
`L₂(α)` has at most `N` vertices, then every empty polytope of `L₃(α)` has at most `N`
times as many vertices as it has distinct first coordinates. -/
theorem main {α : ℝ} {N : ℕ}
    (hN : ∀ W : Set (Fin 2 → ℝ), IsEmptyPolytope (expLattice 2 α) W → W.ncard ≤ N)
    {V : Set (Fin 3 → ℝ)} (hV : IsEmptyPolytope (expLattice 3 α) V) :
    V.ncard ≤ N * ((fun v : Fin 3 → ℝ => v 0) '' V).ncard := by
  classical
  obtain ⟨F, rfl⟩ : ∃ F : Finset (Fin 3 → ℝ), (F : Set (Fin 3 → ℝ)) = V :=
    ⟨hV.1.toFinset, hV.1.coe_toFinset⟩
  have hfiber : ∀ r : ℝ, (F.filter (fun v : Fin 3 → ℝ => v 0 = r)).card ≤ N := by
    intro r
    have hco : ((F.filter (fun v : Fin 3 → ℝ => v 0 = r) : Finset (Fin 3 → ℝ)) :
        Set (Fin 3 → ℝ)) = slice (↑F) r := by
      ext v
      simp [slice, Finset.mem_filter, and_comm]
    have h := slice_ncard_le hN hV r
    rw [← hco, Set.ncard_coe_finset] at h
    exact h
  have hfib : F.card
      = ∑ r ∈ F.image (fun v : Fin 3 → ℝ => v 0),
          (F.filter (fun v : Fin 3 → ℝ => v 0 = r)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)
  have h1 : F.card ≤ (F.image (fun v : Fin 3 → ℝ => v 0)).card * N := by
    calc F.card
        = ∑ r ∈ F.image (fun v : Fin 3 → ℝ => v 0),
            (F.filter (fun v : Fin 3 → ℝ => v 0 = r)).card := hfib
      _ ≤ ∑ _r ∈ F.image (fun v : Fin 3 → ℝ => v 0), N :=
            Finset.sum_le_sum (fun r _ => hfiber r)
      _ = (F.image (fun v : Fin 3 → ℝ => v 0)).card * N := by
            rw [Finset.sum_const, smul_eq_mul]
  have h3 : ((fun v : Fin 3 → ℝ => v 0) '' (↑F : Set (Fin 3 → ℝ))).ncard
      = (F.image (fun v : Fin 3 → ℝ => v 0)).card := by
    rw [← Finset.coe_image, Set.ncard_coe_finset]
  rw [Set.ncard_coe_finset, h3, Nat.mul_comm]
  exact h1


/-- **The statement.**  The slice bound, and the finiteness transfer it gives. -/
theorem proof :
    (∀ α : ℝ, ∀ N : ℕ,
        (∀ W : Set (Fin 2 → ℝ),
            (W.Finite ∧ W ⊆ {x : Fin 2 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
              (∀ w ∈ W, w ∉ convexHull ℝ (W \ {w})) ∧
              convexHull ℝ W ∩ {x : Fin 2 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ W) →
            W.ncard ≤ N) →
        ∀ V : Set (Fin 3 → ℝ),
          (V.Finite ∧ V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
            (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
            convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ V) →
          V.ncard ≤ N * ((fun v : Fin 3 → ℝ => v 0) '' V).ncard) ∧
    (∀ α : ℝ, ∀ N K : ℕ,
        (∀ W : Set (Fin 2 → ℝ),
            (W.Finite ∧ W ⊆ {x : Fin 2 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
              (∀ w ∈ W, w ∉ convexHull ℝ (W \ {w})) ∧
              convexHull ℝ W ∩ {x : Fin 2 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ W) →
            W.ncard ≤ N) →
        (∀ V : Set (Fin 3 → ℝ),
            (V.Finite ∧ V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
              (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
              convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ V) →
            ((fun v : Fin 3 → ℝ => v 0) '' V).ncard ≤ K) →
        ∀ V : Set (Fin 3 → ℝ),
          (V.Finite ∧ V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
            (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
            convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ V) →
          V.ncard ≤ N * K) := by
  refine ⟨fun α N hN V hV => main hN hV, fun α N K hN hK V hV => ?_⟩
  exact le_trans (main hN hV) (Nat.mul_le_mul_left N (hK V hV))

end Submissions.ExpLatticeLevelReduction.Slice
