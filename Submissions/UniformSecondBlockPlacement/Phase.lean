import Mathlib

namespace Submissions.UniformSecondBlockPlacement.Phase

open Complex ComplexConjugate

variable {k : ℕ}

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

lemma nonvanishing_on_torus {p : MvPolynomial (Fin k) ℂ}
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

lemma simultaneous_nonvanishing {N : ℕ}
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

abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

abbrev IsPhase (z : Fin k → ℂ) : Prop := ∀ r, ‖z r‖ = 1

abbrev scale {ι : Type} (z : Fin k → ℂ) (w : ι → Fin k → ℂ) : ι → Fin k → ℂ :=
  fun j r => z r * w j r

abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) : Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

abbrev CoordinateUniform {n : ℕ} (w : Fin n → Fin k → ℂ) : Prop :=
  ∀ (t : ℕ) (b : Fin t → Fin n) (e : Fin t → Fin k),
    Function.Injective b → Function.Injective e →
    LinearIndependent ℂ (fun p => w (b p)) →
    Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0

lemma subfamily_indices
    {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) {t : ℕ}
    (ht : Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = t) :
    ∃ (I : Fin t → ι), Function.Injective I ∧
      Submodule.span ℂ (Set.range (v ∘ I)) = Submodule.span ℂ (Set.range v) ∧
      LinearIndependent ℂ (v ∘ I) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = t := by
    rw [← ht, ← hspan]
    rw [linearIndependent_iff_card_eq_finrank_span] at hli
    change Fintype.card κ = Set.finrank ℂ (Set.range (v ∘ a))
    exact hli
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let I : Fin t → ι := fun i => a (e.symm (Fin.cast hcard.symm i))
  have hI : Function.Injective I := by
    intro i j hij
    apply Fin.cast_injective hcard.symm
    apply e.symm.injective
    apply ha
    exact hij
  refine ⟨I, hI, ?_, ?_⟩
  · have hrange : Set.range I = Set.range a := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm (Fin.cast hcard.symm i), by simp [I, e]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.cast hcard (e i), by simp [I, e]⟩
    rw [← hspan]
    congr 1
    calc
      Set.range (v ∘ I) = v '' Set.range I := Set.range_comp v I
      _ = v '' Set.range a := congrArg (fun s : Set ι => v '' s) hrange
      _ = Set.range (v ∘ a) := (Set.range_comp v a).symm
  · rw [show v ∘ I = (v ∘ a) ∘ (e.symm ∘ Fin.cast hcard.symm) by rfl]
    exact hli.comp _ (e.symm.injective.comp (Fin.cast_injective hcard.symm))

lemma extend_independent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {t d : ℕ} (v : Fin t → V) (hv : LinearIndependent ℂ v)
    (h : t + d ≤ Module.finrank ℂ V) :
    ∃ b : Fin (t + d) → V,
      (∀ i, b (Fin.castAdd d i) = v i) ∧ LinearIndependent ℂ b := by
  induction d generalizing v with
  | zero =>
      refine ⟨v, ?_, hv⟩
      intro i
      rfl
  | succ d ih =>
      have hlt : t + d < Module.finrank ℂ V := by omega
      obtain ⟨b, hb, hbi⟩ := ih v hv (by omega)
      obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hbi hlt
      refine ⟨Fin.snoc b x, ?_, hx⟩
      intro i
      rw [show Fin.castAdd (d + 1) i = (Fin.castAdd d i).castSucc by rfl]
      rw [Fin.snoc_castSucc]
      exact hb i

lemma det_ne_zero_of_rows_li {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : LinearIndependent ℂ (fun i => A i)) : A.det ≠ 0 := by
  rw [← Matrix.nonsingular_iff_det_ne_zero]
  exact Matrix.Nonsingular.of_linearIndependent_row hA

lemma phase_ne_zero {z : Fin k → ℂ} (hz : IsPhase z) (r : Fin k) : z r ≠ 0 := by
  intro h
  have hr := hz r
  rw [h] at hr
  norm_num at hr

noncomputable def phaseEquiv (z : Fin k → ℂ) (hz : ∀ r, z r ≠ 0) :
    (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ) :=
  LinearEquiv.piCongrRight fun r =>
    Units.mulLeftLinearEquiv ℂ ℂ (Units.mk0 (z r) (hz r))

lemma phaseEquiv_apply (z : Fin k → ℂ) (hz : ∀ r, z r ≠ 0)
    (x : Fin k → ℂ) (r : Fin k) :
    phaseEquiv z hz x r = z r * x r := by
  simp [phaseEquiv, Units.mulLeftLinearEquiv]

lemma phase_rank_eq (z : Fin k → ℂ) (hz : ∀ r, z r ≠ 0)
    {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) :
    rk (fun i => phaseEquiv z hz (v i)) S = rk v S := by
  let e := phaseEquiv z hz
  have hmap :
      Submodule.map (e : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))
          (Submodule.span ℂ
            (Set.range (fun i : (S : Set ι) => v i))) =
        Submodule.span ℂ
          (Set.range (fun i : (S : Set ι) => e (v i))) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  unfold rk
  rw [← hmap]
  exact e.finrank_map_eq _

noncomputable def crossPoly {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ)
    (w : Fin n₂ → Fin k → ℂ) (i : Fin n₁) (j : Fin n₂) :
    MvPolynomial (Fin k) ℂ :=
  ∑ r, MvPolynomial.C (star (u i r) * w j r) * MvPolynomial.X r

lemma eval_crossPoly {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ)
    (w : Fin n₂ → Fin k → ℂ) (z : Fin k → ℂ) (i : Fin n₁) (j : Fin n₂) :
    MvPolynomial.eval z (crossPoly u w i j) =
      pair (u i) (scale z w j) := by
  simp [crossPoly, pair, scale, MvPolynomial.eval₂Hom_X']
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma rank_union_le {n₁ n₂ : ℕ}
    (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂)) :
    rk (Sum.elim u w) (S.disjSum T) ≤ rk u S + rk w T := by
  let A := Submodule.span ℂ (Set.range (fun i : (S : Set (Fin n₁)) => u i))
  let B := Submodule.span ℂ (Set.range (fun j : (T : Set (Fin n₂)) => w j))
  have hrange :
      Set.range
          (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
            Sum.elim u w q.1) =
        Set.range (fun i : (S : Set (Fin n₁)) => u i) ∪
          Set.range (fun j : (T : Set (Fin n₂)) => w j) := by
    ext x
    constructor
    · rintro ⟨⟨q, hq⟩, rfl⟩
      rcases q with i | j
      · left
        refine ⟨⟨i, (Finset.inl_mem_disjSum).mp hq⟩, ?_⟩
        change u i = Sum.elim u w (Sum.inl i)
        rfl
      · right
        refine ⟨⟨j, (Finset.inr_mem_disjSum).mp hq⟩, ?_⟩
        change w j = Sum.elim u w (Sum.inr j)
        rfl
    · intro hx
      rcases hx with ⟨⟨i, hi⟩, rfl⟩ | ⟨⟨j, hj⟩, rfl⟩
      · refine ⟨⟨Sum.inl i, Finset.inl_mem_disjSum.mpr hi⟩, ?_⟩
        rfl
      · refine ⟨⟨Sum.inr j, Finset.inr_mem_disjSum.mpr hj⟩, ?_⟩
        rfl
  have hspan :
      Submodule.span ℂ
          (Set.range
            (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
              Sum.elim u w q.1)) = A ⊔ B := by
    dsimp [A, B]
    calc
      Submodule.span ℂ
          (Set.range
            (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
              Sum.elim u w q.1)) =
          Submodule.span ℂ
            (Set.range (fun i : (S : Set (Fin n₁)) => u i) ∪
              Set.range (fun j : (T : Set (Fin n₂)) => w j)) :=
        congrArg (Submodule.span ℂ) hrange
      _ = _ := Submodule.span_union _ _
  change Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
            Sum.elim u w q.1))) ≤
      Module.finrank ℂ A + Module.finrank ℂ B
  rw [hspan]
  exact Submodule.finrank_add_le_finrank_add_finrank A B

def splitPoly {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ)
    (w : Fin n₂ → Fin k → ℂ) (ta tb : ℕ)
    (a : Fin ta → Fin n₁) (b : Fin tb → Fin n₂)
    (c : Fin ta → Fin k) (e : Fin tb → Fin k) :
    Matrix (Fin ta ⊕ Fin tb) (Fin ta ⊕ Fin tb)
      (MvPolynomial (Fin k) ℂ) :=
  Matrix.fromBlocks
    (fun p q => MvPolynomial.C (u (a p) (c q)))
    (fun p q => MvPolynomial.C (u (a p) (e q)))
    (fun q p => MvPolynomial.X (c p) * MvPolynomial.C (w (b q) (c p)))
    (fun q p => MvPolynomial.X (e p) * MvPolynomial.C (w (b q) (e p)))

lemma splitPoly_ne_zero {n₁ n₂ : ℕ}
    (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (ta tb : ℕ) (a : Fin ta → Fin n₁) (b : Fin tb → Fin n₂)
    (c : Fin ta → Fin k) (e : Fin tb → Fin k)
    (hce : ∀ p q, c p ≠ e q)
    (hA : Matrix.det (Matrix.of fun p q => u (a p) (c q)) ≠ 0)
    (hD : Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0) :
    (splitPoly u w ta tb a b c e).det ≠ 0 := by
  let y : Fin k → Polynomial ℂ := fun r =>
    if r ∈ Set.range c then 0
    else if r ∈ Set.range e then Polynomial.X
    else 0
  let φ := MvPolynomial.eval₂Hom Polynomial.C y
  have hyc (i : Fin ta) : y (c i) = 0 := by
    simp [y]
  have hye (i : Fin tb) : y (e i) = Polynomial.X := by
    have hnot : e i ∉ Set.range c := by
      rintro ⟨j, hj⟩
      exact hce j i hj
    simp only [y, if_neg hnot]
    rw [if_pos (show e i ∈ Set.range e from ⟨i, rfl⟩)]
  let A' : Matrix (Fin ta) (Fin ta) (Polynomial ℂ) :=
    fun i j => Polynomial.C (u (a i) (c j))
  let D' : Matrix (Fin tb) (Fin tb) (Polynomial ℂ) :=
    fun i j => Polynomial.C (w (b i) (e j))
  have hm :
      φ.mapMatrix (splitPoly u w ta tb a b c e) =
        (Matrix.fromBlocks
          A'
          (fun i j => Polynomial.C (u (a i) (e j)))
          (0 : Matrix (Fin tb) (Fin ta) (Polynomial ℂ))
          ((Polynomial.X : Polynomial ℂ) • D') :
            Matrix (Fin ta ⊕ Fin tb) (Fin ta ⊕ Fin tb) (Polynomial ℂ)) := by
    rw [RingHom.mapMatrix_apply]
    funext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [splitPoly, Matrix.fromBlocks, Matrix.map_apply, Matrix.of_apply]
      change φ (MvPolynomial.C (u (a i) (c j))) = Polynomial.C (u (a i) (c j))
      exact MvPolynomial.eval₂Hom_C _ _ _
    · simp only [splitPoly, Matrix.fromBlocks, Matrix.map_apply, Matrix.of_apply]
      change φ (MvPolynomial.C (u (a i) (e j))) = Polynomial.C (u (a i) (e j))
      exact MvPolynomial.eval₂Hom_C _ _ _
    · simp only [splitPoly, Matrix.fromBlocks, Matrix.map_apply, Matrix.of_apply]
      change φ (MvPolynomial.X (c j) * MvPolynomial.C (w (b i) (c j))) = 0
      rw [map_mul, MvPolynomial.eval₂Hom_X', hyc, MvPolynomial.eval₂Hom_C]
      simp
    · simp only [splitPoly, Matrix.fromBlocks, Matrix.map_apply, Matrix.of_apply]
      change φ (MvPolynomial.X (e j) * MvPolynomial.C (w (b i) (e j))) =
        (Polynomial.X • D') i j
      rw [map_mul, MvPolynomial.eval₂Hom_X', hye,
        MvPolynomial.eval₂Hom_C]
      rfl
  have hAd : A'.det = Polynomial.C
      (Matrix.det (Matrix.of fun p q => u (a p) (c q))) := by
    change (Matrix.of fun p q => Polynomial.C (u (a p) (c q))).det =
      Polynomial.C (Matrix.det (Matrix.of fun p q => u (a p) (c q)))
    exact (RingHom.map_det Polynomial.C _).symm
  have hDd : D'.det = Polynomial.C
      (Matrix.det (Matrix.of fun p q => w (b p) (e q))) := by
    change (Matrix.of fun p q => Polynomial.C (w (b p) (e q))).det =
      Polynomial.C (Matrix.det (Matrix.of fun p q => w (b p) (e q)))
    exact (RingHom.map_det Polynomial.C _).symm
  have hdet :
      φ ((splitPoly u w ta tb a b c e).det) =
        A'.det * ((Polynomial.X : Polynomial ℂ) • D').det := by
    calc
      φ ((splitPoly u w ta tb a b c e).det) =
          (φ.mapMatrix (splitPoly u w ta tb a b c e)).det :=
        RingHom.map_det φ _
      _ = (Matrix.fromBlocks A'
          (fun i j => Polynomial.C (u (a i) (e j)))
          (0 : Matrix (Fin tb) (Fin ta) (Polynomial ℂ))
          ((Polynomial.X : Polynomial ℂ) • D')).det := congrArg Matrix.det hm
      _ = A'.det * ((Polynomial.X : Polynomial ℂ) • D').det :=
        Matrix.det_fromBlocks_zero₂₁ _ _ _
  have hnon : φ ((splitPoly u w ta tb a b c e).det) ≠ 0 := by
    rw [hdet, Matrix.det_smul, hAd, hDd]
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr hA
    · apply mul_ne_zero
      · exact pow_ne_zero (Fintype.card (Fin tb)) Polynomial.X_ne_zero
      · exact Polynomial.C_ne_zero.mpr hD
  intro hp
  apply hnon
  rw [hp]
  exact map_zero φ

lemma split_det_witness
    {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂))
    {ta tb : ℕ} (a : Fin ta → Fin n₁) (b : Fin tb → Fin n₂)
    (c : Fin ta → Fin k) (e : Fin tb → Fin k)
    (ht : ta + tb = min k (rk u S + rk w T))
    (ha : ∀ p, a p ∈ S) (hb : ∀ q, b q ∈ T)
    (hce : ∀ p q, c p ≠ e q)
    (hA : Matrix.det (Matrix.of fun p q => u (a p) (c q)) ≠ 0)
    (hD : Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0) :
    ∃ p : MvPolynomial (Fin k) ℂ, p ≠ 0 ∧
      ∀ z : Fin k → ℂ, MvPolynomial.eval z p ≠ 0 →
        min k (rk u S + rk w T) ≤
          rk (Sum.elim u (scale z w)) (S.disjSum T) := by
  let P := splitPoly u w ta tb a b c e
  have hP : P.det ≠ 0 := by
    exact splitPoly_ne_zero u w ta tb a b c e hce hA hD
  let col : (Fin ta ⊕ Fin tb) → Fin k := Sum.elim c e
  let sel (z : Fin k → ℂ) : (Fin ta ⊕ Fin tb) → Fin k → ℂ :=
    Sum.elim (fun p => u (a p))
      (fun q r => z r * w (b q) r)
  let M (z : Fin k → ℂ) :
      Matrix (Fin ta ⊕ Fin tb) (Fin ta ⊕ Fin tb) ℂ :=
    fun i j => sel z i (col j)
  have heval (z : Fin k → ℂ) :
      MvPolynomial.eval z P.det = (M z).det := by
    let φ := MvPolynomial.eval₂Hom (RingHom.id ℂ) z
    have hmap := RingHom.map_det φ P
    have hm : φ.mapMatrix P = M z := by
      rw [RingHom.mapMatrix_apply]
      funext i j
      rcases i with i | i <;> rcases j with j | j
      · simp only [P, splitPoly, M, sel, col, Matrix.fromBlocks,
          Matrix.map_apply, Matrix.of_apply]
        change φ (MvPolynomial.C (u (a i) (c j))) = u (a i) (c j)
        exact MvPolynomial.eval₂Hom_C _ _ _
      · simp only [P, splitPoly, M, sel, col, Matrix.fromBlocks,
          Matrix.map_apply, Matrix.of_apply]
        change φ (MvPolynomial.C (u (a i) (e j))) = u (a i) (e j)
        exact MvPolynomial.eval₂Hom_C _ _ _
      · simp only [P, splitPoly, M, sel, col, Matrix.fromBlocks,
          Matrix.map_apply, Matrix.of_apply]
        change φ (MvPolynomial.X (c j) * MvPolynomial.C (w (b i) (c j))) =
          z (c j) * w (b i) (c j)
        rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
        rfl
      · simp only [P, splitPoly, M, sel, col, Matrix.fromBlocks,
          Matrix.map_apply, Matrix.of_apply]
        change φ (MvPolynomial.X (e j) * MvPolynomial.C (w (b i) (e j))) =
          z (e j) * w (b i) (e j)
        rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
        rfl
    change φ P.det = (M z).det
    calc
      φ P.det = (φ.mapMatrix P).det := hmap
      _ = (M z).det := by rw [hm]
  refine ⟨P.det, hP, ?_⟩
  intro z hz
  have hMz : (M z).det ≠ 0 := by
    rw [← heval z]
    exact hz
  have hrows : LinearIndependent ℂ (fun i => M z i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hMz
  let L : (Fin k → ℂ) →ₗ[ℂ] ((Fin ta ⊕ Fin tb) → ℂ) :=
    { toFun := fun x q => x (col q)
      map_add' := by
        intro x y
        funext q
        simp
      map_smul' := by
        intro r x
        funext q
        simp }
  have hcomp : LinearIndependent ℂ (L ∘ sel z) := by
    have heq : L ∘ sel z = fun i => M z i := by
      funext i
      rfl
    rw [heq]
    exact hrows
  have hsel : LinearIndependent ℂ (sel z) :=
    LinearIndependent.of_comp L hcomp
  have hdim :
    min k (rk u S + rk w T) ≤
        Module.finrank ℂ
          (Submodule.span ℂ (Set.range (sel z))) := by
    have hh := (linearIndependent_iff_card_eq_finrank_span.mp hsel).symm
    have hh' : Module.finrank ℂ
        (Submodule.span ℂ (Set.range (sel z))) = ta + tb := by
      simpa [Fintype.card_sum, Set.finrank] using hh
    rw [hh', ← ht]
  let ι :
      (Fin ta ⊕ Fin tb) →
        ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) :=
    fun q =>
      match q with
      | Sum.inl p => ⟨Sum.inl (a p), Finset.inl_mem_disjSum.mpr (ha p)⟩
      | Sum.inr q => ⟨Sum.inr (b q), Finset.inr_mem_disjSum.mpr (hb q)⟩
  have hmono :
      Submodule.span ℂ (Set.range (sel z)) ≤
        Submodule.span ℂ
          (Set.range
            (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
              Sum.elim u (scale z w) q.1)) := by
    apply Submodule.span_mono
    rintro x ⟨q, rfl⟩
    refine ⟨ι q, ?_⟩
    cases q <;> rfl
  calc
    min k (rk u S + rk w T) ≤
        Module.finrank ℂ (Submodule.span ℂ (Set.range (sel z))) := hdim
    _ ≤ Module.finrank ℂ
        (Submodule.span ℂ
          (Set.range
            (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
              Sum.elim u (scale z w) q.1))) :=
      Submodule.finrank_mono hmono

lemma det_witness
    {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (S : Finset (Fin n₁)) (T : Finset (Fin n₂))
    {z₀ : Fin k → ℂ} (hz₀ : IsPhase z₀)
    (h₀ :
      rk (Sum.elim u (scale z₀ w)) (S.disjSum T) =
        min k (rk u S + rk w T)) :
    ∃ p : MvPolynomial (Fin k) ℂ, p ≠ 0 ∧
      ∀ z : Fin k → ℂ, MvPolynomial.eval z p ≠ 0 →
        min k (rk u S + rk w T) ≤
          rk (Sum.elim u (scale z w)) (S.disjSum T) := by
  let t := min k (rk u S + rk w T)
  have ht : t ≤ k := Nat.min_le_left _ _
  let d := k - t
  have htd : t + d = k := Nat.add_sub_of_le ht
  let v₀ : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) → Fin k → ℂ :=
    fun q => Sum.elim u (scale z₀ w) q.1
  have hv₀ : Module.finrank ℂ (Submodule.span ℂ (Set.range v₀)) = t := by
    simpa [v₀, t, rk] using h₀
  obtain ⟨I, hI, hspan, hli⟩ := subfamily_indices v₀ hv₀
  have hdim : t + d ≤ Module.finrank ℂ (Fin k → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simpa using le_of_eq htd
  obtain ⟨b, hb, hbi⟩ := extend_independent (v₀ ∘ I) hli hdim
  let aux : Fin d → Fin k → ℂ := fun q => b (Fin.natAdd t q)
  let rows (z : Fin k → ℂ) : Fin (t + d) → Fin k → ℂ :=
    Fin.addCases
      (fun i => Sum.elim u (scale z w) (I i).1)
      aux
  have hrows₀ : LinearIndependent ℂ (rows z₀) := by
    have heq : rows z₀ = b := by
      funext q
      by_cases hq : q.val < t
      · let i : Fin t := ⟨q.val, hq⟩
        have hqi : q = Fin.castAdd d i := by
          apply Fin.ext
          rfl
        rw [hqi]
        simp [rows, Fin.addCases_left]
        exact (hb i).symm
      · have hq' : t ≤ q.val := Nat.le_of_not_gt hq
        let j : Fin d := ⟨q.val - t, by omega⟩
        have hqj : q = Fin.natAdd t j := by
          apply Fin.ext
          simp [j]
          omega
        rw [hqj]
        change Fin.addCases
          (fun i => Sum.elim u (scale z₀ w) (I i).1) aux
          (Fin.natAdd t j) = b (Fin.natAdd t j)
        rw [Fin.addCases_right]
    rw [heq]
    exact hbi
  let rowIndex : Fin k → Fin (t + d) := fun i => Fin.cast htd.symm i
  let A (z : Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
    fun i r => rows z (rowIndex i) r
  let polyEntry (q : Sum (Fin n₁) (Fin n₂)) (r : Fin k) :
      MvPolynomial (Fin k) ℂ :=
    match q with
    | Sum.inl i => MvPolynomial.C (u i r)
    | Sum.inr j => MvPolynomial.X r * MvPolynomial.C (w j r)
  let P : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k) ℂ) :=
    fun i r =>
      Fin.addCases
        (fun a => polyEntry (I a).1 r)
        (fun q => MvPolynomial.C (aux q r))
        (rowIndex i)
  let p : MvPolynomial (Fin k) ℂ := P.det
  have hrowIndex : Function.Injective rowIndex := Fin.cast_injective htd.symm
  have hA₀ : LinearIndependent ℂ (fun i => A z₀ i) := by
    change LinearIndependent ℂ (fun i => rows z₀ (rowIndex i))
    exact hrows₀.comp rowIndex hrowIndex
  have hdet₀ : (A z₀).det ≠ 0 := det_ne_zero_of_rows_li _ hA₀
  have heval (z : Fin k → ℂ) :
      MvPolynomial.eval z p = (A z).det := by
    let φ := MvPolynomial.eval₂Hom (RingHom.id ℂ) z
    have hmap := RingHom.map_det φ P
    have hmatrix : φ.mapMatrix P = A z := by
      rw [RingHom.mapMatrix_apply]
      funext i r
      change φ (P i r) = A z i r
      dsimp [P, A, rows, rowIndex, polyEntry]
      let q := Fin.cast htd.symm i
      by_cases hq : q.val < t
      · let a : Fin t := ⟨q.val, hq⟩
        have hqa : q = Fin.castAdd d a := by
          apply Fin.ext
          rfl
        change φ (Fin.addCases
          (fun a => polyEntry (I a).1 r)
          (fun q => MvPolynomial.C (aux q r)) q) =
          Fin.addCases
            (fun i => Sum.elim u (scale z w) (I i).1) aux q r
        rw [hqa, Fin.addCases_left]
        simp [φ, polyEntry, scale, Sum.elim]
        cases I a with
        | mk q hq =>
            cases q <;> simp [polyEntry, scale, Sum.elim]
      · have hq' : t ≤ q.val := Nat.le_of_not_gt hq
        let a : Fin d := ⟨q.val - t, by omega⟩
        have hqa : q = Fin.natAdd t a := by
          apply Fin.ext
          simp [a]
          omega
        change φ (Fin.addCases
          (fun a => polyEntry (I a).1 r)
          (fun q => MvPolynomial.C (aux q r)) q) =
          Fin.addCases
            (fun i => Sum.elim u (scale z w) (I i).1) aux q r
        rw [hqa, Fin.addCases_right]
        simp [φ, aux]
    change φ p = (A z).det
    calc
      φ p = φ P.det := by rfl
      _ = (φ.mapMatrix P).det := hmap
      _ = (A z).det := by rw [hmatrix]
  have hp : p ≠ 0 := by
    intro hp
    have : MvPolynomial.eval z₀ p = 0 := by rw [hp]; simp
    rw [heval z₀] at this
    exact hdet₀ this
  refine ⟨p, hp, ?_⟩
  intro z hz
  have hAz : LinearIndependent ℂ (fun i => A z i) := by
    apply Matrix.linearIndependent_rows_of_det_ne_zero
    exact (show (A z).det ≠ 0 by rw [← heval z]; exact hz)
  have hsel : LinearIndependent ℂ (fun i : Fin t =>
      Sum.elim u (scale z w) (I i).1) := by
    let f : Fin t → Fin k := fun i => Fin.cast htd (Fin.castAdd d i)
    have hf : Function.Injective f :=
      (Fin.cast_injective htd).comp (Fin.castAdd_injective t d)
    have hcomp := hAz.comp f hf
    have hrow :
        (fun i : Fin t => A z (f i)) =
          (fun i : Fin t => Sum.elim u (scale z w) (I i).1) := by
      funext i
      simp [A, f, rowIndex, rows, Fin.addCases_left]
    rw [← hrow]
    exact hcomp
  have hspanle :
      t ≤ rk (Sum.elim u (scale z w)) (S.disjSum T) := by
    have hdimsel : Module.finrank ℂ
        (Submodule.span ℂ (Set.range
          (fun i : Fin t => Sum.elim u (scale z w) (I i).1))) = t := by
      have hh := (linearIndependent_iff_card_eq_finrank_span.mp hsel).symm
      simpa [Set.finrank] using hh
    rw [← hdimsel]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    intro x hx
    rcases hx with ⟨i, rfl⟩
    refine ⟨I i, ?_⟩
    rfl
  exact hspanle

lemma simultaneous_finite {α : Type*} [Fintype α]
    (p : α → MvPolynomial (Fin k) ℂ) (hp : ∀ a, p a ≠ 0) :
    ∃ z : Fin k → ℂ,
      (∀ r, ‖z r‖ = 1) ∧ ∀ a, MvPolynomial.eval z (p a) ≠ 0 := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  obtain ⟨z, hz, hne⟩ :=
    simultaneous_nonvanishing
      (fun i => p (e.symm i)) (fun i => hp (e.symm i))
  refine ⟨z, hz, ?_⟩
  intro a
  simpa using hne (e a)

theorem old_target : ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      (∀ (i : Fin n₁) (j : Fin n₂),
        ∃ z : Fin k → ℂ, IsPhase z ∧
          pair (u i) (scale z w j) ≠ 0) →
      (∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
        ∃ z : Fin k → ℂ, IsPhase z ∧
          rk (Sum.elim u (scale z w)) (S.disjSum T) =
            min k (rk u S + rk w T)) →
      ∃ z : Fin k → ℂ, IsPhase z ∧
        (∀ (i : Fin n₁) (j : Fin n₂),
          pair (u i) (scale z w j) ≠ 0) ∧
        Transversal u (scale z w) := by
  intro k n₁ n₂ hk u w hcross htrans
  classical
  let α : Type :=
    Sum (Fin n₁ × Fin n₂)
      (Finset (Fin n₁) × Finset (Fin n₂))
  have detData :
      ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
        ∃ p : MvPolynomial (Fin k) ℂ, p ≠ 0 ∧
          ∀ z : Fin k → ℂ, MvPolynomial.eval z p ≠ 0 →
            min k (rk u S + rk w T) ≤
              rk (Sum.elim u (scale z w)) (S.disjSum T) := by
    intro S T
    obtain ⟨z₀, hz₀, h₀⟩ := htrans S T
    exact det_witness u w S T hz₀ h₀
  let p : α → MvPolynomial (Fin k) ℂ :=
    Sum.elim
      (fun ij => crossPoly u w ij.1 ij.2)
      (fun ST =>
        Classical.choose (detData ST.1 ST.2))
  have hp : ∀ a, p a ≠ 0 := by
    intro a
    cases a with
    | inl ij =>
        have hsome := hcross ij.1 ij.2
        obtain ⟨z, hz, hne⟩ := hsome
        intro hzero
        apply hne
        have hzero' : crossPoly u w ij.1 ij.2 = 0 := by
          simpa [p] using hzero
        rw [← eval_crossPoly u w z ij.1 ij.2, hzero']
        simp
    | inr ST =>
        exact (Classical.choose_spec (detData ST.1 ST.2)).1
  obtain ⟨z, hz, hne⟩ := simultaneous_finite p hp
  have hz0 : ∀ r, z r ≠ 0 := fun r => phase_ne_zero hz r
  have hcross' : ∀ (i : Fin n₁) (j : Fin n₂),
      pair (u i) (scale z w j) ≠ 0 := by
    intro i j hzero
    have he : MvPolynomial.eval z (p (Sum.inl (i, j))) ≠ 0 :=
      hne (Sum.inl (i, j))
    apply he
    simpa [p, eval_crossPoly u w z i j] using hzero
  have htrans' : Transversal u (scale z w) := by
    intro S T
    let t := min k (rk u S + rk w T)
    have hlower : t ≤ rk (Sum.elim u (scale z w)) (S.disjSum T) := by
      let q : α := Sum.inr (S, T)
      have hq := hne q
      dsimp [q, p] at hq
      exact (Classical.choose_spec (detData S T)).2 z hq
    have hphase :
        rk (scale z w) T = rk w T := by
      have heq : scale z w =
          (fun j => phaseEquiv z hz0 (w j)) := by
        funext j r
        exact (phaseEquiv_apply z hz0 (w j) r).trans rfl
      rw [heq]
      exact phase_rank_eq z hz0 w T
    have hupp :
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤
          rk u S + rk w T := by
      calc
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤
            rk u S + rk (scale z w) T := rank_union_le u (scale z w) S T
        _ = rk u S + rk w T := by rw [hphase]
    have hdim :
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤ k := by
      change Module.finrank ℂ
          (Submodule.span ℂ
            (Set.range
              (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
                Sum.elim u (scale z w) q.1))) ≤ k
      have hfin := Submodule.finrank_mono
        (show Submodule.span ℂ
            (Set.range
              (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
                Sum.elim u (scale z w) q.1)) ≤ ⊤ from le_top)
      simpa [Module.finrank_fintype_fun_eq_card] using hfin
    have hmin :
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤ k ∧
          rk (Sum.elim u (scale z w)) (S.disjSum T) ≤
            rk u S + rk (scale z w) T := by
      exact ⟨hdim, by simpa [hphase] using hupp⟩
    exact Nat.le_antisymm (Nat.le_min.mpr hmin) (by
      rw [hphase]
      simpa [t] using hlower)
  exact ⟨z, hz, hcross', htrans'⟩

lemma crossPoly_ne_zero_of_support {n₁ n₂ : ℕ}
    (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ)
    (i : Fin n₁) (j : Fin n₂) (r : Fin k)
    (hu : u i r ≠ 0) (hw : w j r ≠ 0) :
    crossPoly u w i j ≠ 0 := by
  rw [MvPolynomial.ne_zero_iff]
  refine ⟨Finsupp.single r 1, ?_⟩
  simp only [crossPoly, Finset.sum_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X_mul]
  classical
  rw [Finset.sum_eq_single r]
  · simpa using (mul_ne_zero (star_ne_zero.mpr hu) hw)
  · intro b hb hbr
    simp [hbr]
  · simp

lemma coordinate_minor_of_linearIndependent
    {a : ℕ} {v : Fin a → Fin k → ℂ}
    (hv : LinearIndependent ℂ v) :
    ∃ e : Fin a → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q => v p (e q)) ≠ 0 := by
  let A : Matrix (Fin a) (Fin k) ℂ := fun p r => v p r
  have hArank : A.rank = a := by
    calc
      A.rank = Module.finrank ℂ
          (Submodule.span ℂ (Set.range A.row)) :=
        A.rank_eq_finrank_span_row
      _ = Fintype.card (Fin a) := by
        rw [linearIndependent_iff_card_eq_finrank_span.mp hv]
        rfl
      _ = a := Fintype.card_fin a
  have hcolrank :
      Module.finrank ℂ (Submodule.span ℂ (Set.range A.col)) = a := by
    rw [← Matrix.rank_eq_finrank_span_cols A, hArank]
  obtain ⟨κ, e₀, he₀, hspan, hli⟩ :=
    exists_linearIndependent' ℂ A.col
  letI : Finite κ := Finite.of_injective e₀ he₀
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = a := by
    rw [← hcolrank, ← hspan]
    rw [linearIndependent_iff_card_eq_finrank_span] at hli
    change Fintype.card κ = Set.finrank ℂ (Set.range (A.col ∘ e₀))
    exact hli
  let efin : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let e : Fin a → Fin k :=
    fun i => e₀ (efin.symm (Fin.cast hcard.symm i))
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.cast_injective hcard.symm
    exact efin.symm.injective (he₀ hij)
  let M : Matrix (Fin a) (Fin a) ℂ :=
    Matrix.of fun p q => v p (e q)
  have hMcols : LinearIndependent ℂ M.col := by
    have heq : M.col = A.col ∘ e := by
      funext q p
      rfl
    rw [heq]
    have hf : Function.Injective
        (efin.symm ∘ (Fin.cast hcard.symm)) :=
      efin.symm.injective.comp (Fin.cast_injective hcard.symm)
    exact hli.comp _ hf
  have hMrows : LinearIndependent ℂ (Matrix.transpose M).row := by
    simpa [Matrix.col] using hMcols
  refine ⟨e, he, ?_⟩
  rw [← Matrix.det_transpose M]
  exact det_ne_zero_of_rows_li (Matrix.transpose M) hMrows

lemma exists_disjoint_coordinates
    {a tb : ℕ} (c : Fin a → Fin k) (hc : Function.Injective c)
    (htb : tb ≤ k - a) :
    ∃ e : Fin tb → Fin k, Function.Injective e ∧
      ∀ p q, c p ≠ e q := by
  let image : Finset (Fin k) := Finset.univ.image c
  let complement : Finset (Fin k) := Finset.univ \ image
  have himage : image.card = a := by
    simp [image, Finset.card_image_of_injective _ hc]
  have hsubset : image ⊆ Finset.univ := by
    intro x hx
    simp
  have hcard : complement.card = k - a := by
    dsimp [complement]
    rw [Finset.card_sdiff_of_subset hsubset]
    simp [image, himage]
  let ef : complement ≃ Fin (Fintype.card complement) := Fintype.equivFin complement
  have htb' : tb ≤ Fintype.card complement := by
    simpa [hcard] using htb
  let e : Fin tb → Fin k :=
    fun q => (ef.symm (Fin.castLE htb' q)).1
  have he : Function.Injective e := by
    intro p q hpq
    have hsub :
        ef.symm (Fin.castLE htb' p) =
          ef.symm (Fin.castLE htb' q) := by
      apply Subtype.ext
      exact hpq
    exact (Fin.castLE_injective htb') (ef.symm.injective hsub)
  refine ⟨e, he, ?_⟩
  intro p q
  have hmem :
      (ef.symm (Fin.castLE htb' q)).1 ∈ complement :=
    (ef.symm (Fin.castLE htb' q)).2
  have hnot : e q ∉ image := (Finset.mem_sdiff.mp hmem).2
  intro hpq
  apply hnot
  apply Finset.mem_image.mpr
  exact ⟨p, Finset.mem_univ _, hpq⟩

lemma rank_le_ambient {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) :
    rk v S ≤ k := by
  change Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range (fun i : (S : Set ι) => v i))) ≤ k
  have hfin := Submodule.finrank_mono
    (show Submodule.span ℂ
        (Set.range (fun i : (S : Set ι) => v i)) ≤ ⊤ from le_top)
  simpa [Module.finrank_fintype_fun_eq_card] using hfin

theorem target : ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      (∀ i : Fin n₁, u i ≠ 0) →
      (∀ j : Fin n₂, w j ≠ 0) →
      CoordinateUniform w →
      ∃ z : Fin k → ℂ, IsPhase z ∧
        (∀ (i : Fin n₁) (j : Fin n₂),
          pair (u i) (scale z w j) ≠ 0) ∧
        Transversal u (scale z w) := by
  intro k n₁ n₂ hk u w hu hw hcoord
  have hcross' :
      ∀ (i : Fin n₁) (j : Fin n₂),
        ∃ z : Fin k → ℂ, IsPhase z ∧
          pair (u i) (scale z w j) ≠ 0 := by
    intro i j
    obtain ⟨r, hur⟩ : ∃ r, u i r ≠ 0 := by
      by_contra h
      apply hu i
      funext r
      exact Classical.byContradiction (fun hr => h ⟨r, hr⟩)
    have hli : LinearIndependent ℂ (fun _ : Fin 1 => w j) := by
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg q
      have hfg0 : f 0 • w j = g 0 • w j := by
        simpa using hfg
      have hzero : (f 0 - g 0) • w j = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.mpr hfg0
      have hscalar : f 0 - g 0 = 0 :=
        (smul_eq_zero.mp hzero).resolve_right (hw j)
      simpa [Fin.eq_zero q] using sub_eq_zero.mp hscalar
    have hb : Function.Injective (fun _ : Fin 1 => j) := by
      intro p q hpq
      exact Fin.ext (by simpa using congrArg (fun x => x.val) hpq)
    have he : Function.Injective (fun _ : Fin 1 => r) := by
      intro p q hpq
      exact Fin.ext (by simpa using congrArg (fun x => x.val) hpq)
    have hentry :=
      hcoord 1 (fun _ : Fin 1 => j) (fun _ : Fin 1 => r) hb he hli
    have hwr : w j r ≠ 0 := by
      simpa [Matrix.det_fin_one, Matrix.of_apply] using hentry
    have hp : crossPoly u w i j ≠ 0 :=
      crossPoly_ne_zero_of_support u w i j r hur hwr
    obtain ⟨z, hz, hne⟩ := nonvanishing_on_torus hp
    exact ⟨z, hz, by simpa [eval_crossPoly u w z i j] using hne⟩
  have hminor :
      ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
        ∃ (ta tb : ℕ) (a : Fin ta → Fin n₁) (b : Fin tb → Fin n₂)
          (c : Fin ta → Fin k) (e : Fin tb → Fin k),
          ta + tb = min k (rk u S + rk w T) ∧
          (∀ p, a p ∈ S) ∧ (∀ q, b q ∈ T) ∧
          Function.Injective a ∧ Function.Injective b ∧
          Function.Injective c ∧ Function.Injective e ∧
          (∀ p q, c p ≠ e q) ∧
          Matrix.det (Matrix.of fun p q => u (a p) (c q)) ≠ 0 ∧
          Matrix.det (Matrix.of fun p q => w (b p) (e q)) ≠ 0 := by
    intro S T
    let aa := rk u S
    let bb := rk w T
    let tt := min k (aa + bb)
    let tb := tt - aa
    have haa : aa ≤ k := by
      exact rank_le_ambient u S
    have haas : aa ≤ aa + bb := Nat.le_add_right _ _
    have haat : aa ≤ tt := (Nat.le_min).2 ⟨haa, haas⟩
    have htt : tt ≤ k := Nat.min_le_left _ _
    have htb : tb ≤ bb := by
      rw [Nat.sub_le_iff_le_add]
      dsimp [tb, tt]
      omega
    have htbk : tb ≤ k - aa := by
      dsimp [tb]
      exact Nat.sub_le_sub_right htt aa
    have hrankS :
        Module.finrank ℂ
            (Submodule.span ℂ
              (Set.range (fun i : (S : Set (Fin n₁)) => u i))) = aa := by
      rfl
    obtain ⟨ai, hai, hAspan, hAi⟩ :=
      subfamily_indices (fun i : (S : Set (Fin n₁)) => u i) hrankS
    let a : Fin aa → Fin n₁ := fun p => (ai p).1
    have hia : Function.Injective a := by
      intro p q hpq
      exact hai (Subtype.ext hpq)
    have ha_mem : ∀ p, a p ∈ S := by
      intro p
      exact (ai p).2
    have ha_li : LinearIndependent ℂ (fun p => u (a p)) := by
      simpa [a, Function.comp_def] using hAi
    obtain ⟨c, hic, hA⟩ := coordinate_minor_of_linearIndependent ha_li
    have hrankT :
        Module.finrank ℂ
            (Submodule.span ℂ
              (Set.range (fun j : (T : Set (Fin n₂)) => w j))) = bb := by
      rfl
    obtain ⟨bi, hbi, hBspan, hBi⟩ :=
      subfamily_indices (fun j : (T : Set (Fin n₂)) => w j) hrankT
    let b : Fin tb → Fin n₂ :=
      fun q => (bi (Fin.castLE htb q)).1
    have hib : Function.Injective b := by
      intro p q hpq
      change (bi (Fin.castLE htb p)).1 =
        (bi (Fin.castLE htb q)).1 at hpq
      exact Fin.castLE_injective htb (hbi (Subtype.ext hpq))
    have hb_mem : ∀ q, b q ∈ T := by
      intro q
      exact (bi (Fin.castLE htb q)).2
    have hb_li : LinearIndependent ℂ (fun q => w (b q)) := by
      have hcomp := hBi.comp _ (Fin.castLE_injective htb)
      simpa [b, Function.comp_def] using hcomp
    obtain ⟨e, hie, hce⟩ := exists_disjoint_coordinates c hic htbk
    have hD := hcoord tb b e hib hie hb_li
    refine ⟨aa, tb, a, b, c, e, ?_, ha_mem, hb_mem,
      hia, hib, hic, hie, hce, hA, hD⟩
    dsimp [tt, tb]
    omega
  have htrans :
      ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
        ∃ z : Fin k → ℂ, IsPhase z ∧
          rk (Sum.elim u (scale z w)) (S.disjSum T) =
            min k (rk u S + rk w T) := by
    intro S T
    obtain ⟨ta, tb, a, b, c, e, ht, ha, hb, hia, hib, hic, hie, hce, hA, hD⟩ :=
      hminor S T
    obtain ⟨p, hp, hbound⟩ :=
      split_det_witness u w S T a b c e ht ha hb hce hA hD
    obtain ⟨z, hz, hne⟩ := nonvanishing_on_torus hp
    have hz0 : ∀ r, z r ≠ 0 := fun r => phase_ne_zero hz r
    have hupper1 :
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤
          rk u S + rk w T := by
      calc
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤
            rk u S + rk (scale z w) T := rank_union_le u (scale z w) S T
        _ = rk u S + rk w T := by
          congr 1
          have heq : scale z w =
              (fun j => phaseEquiv z hz0 (w j)) := by
            funext j r
            exact (phaseEquiv_apply z hz0 (w j) r).trans rfl
          rw [heq]
          exact phase_rank_eq z hz0 w T
    have hupper2 :
        rk (Sum.elim u (scale z w)) (S.disjSum T) ≤ k := by
      change Module.finrank ℂ
          (Submodule.span ℂ
            (Set.range
              (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
                Sum.elim u (scale z w) q.1))) ≤ k
      have hfin := Submodule.finrank_mono
        (show Submodule.span ℂ
            (Set.range
              (fun q : ((S.disjSum T : Finset (Fin n₁ ⊕ Fin n₂)) : Set _) =>
                Sum.elim u (scale z w) q.1)) ≤ ⊤ from le_top)
      simpa [Module.finrank_fintype_fun_eq_card] using hfin
    refine ⟨z, hz, ?_⟩
    exact Nat.le_antisymm
      (Nat.le_min.mpr ⟨hupper2, hupper1⟩)
      (hbound z hne)
  exact old_target k n₁ n₂ hk u w hcross' htrans

end

end Submissions.UniformSecondBlockPlacement.Phase
