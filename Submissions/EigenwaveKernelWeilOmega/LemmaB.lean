import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

namespace Submissions.EigenwaveKernelWeilOmega.LemmaB

open ExteriorAlgebra

open ExteriorAlgebra

/-- `Γ₁ ⊗ K ⊕ Γ₂ ⊗ K`, both halves indexed by `T`. -/
abbrev Wd (K : Type) [CommRing K] (T : Type) : Type := (T → K) × (T → K)

/-- `⋀(Γ₁ ⊕ Γ₂)`, inside which `⋀^q Γ₁ ⊗ ⋀^r Γ₂` is the span of the products
`γ_{i₁} ⋯ γ_{i_q} e_{j₁} ⋯ e_{j_r}`. -/
abbrev EAd (K : Type) [CommRing K] (T : Type) : Type := ExteriorAlgebra K (Wd K T)

/-- The square-zero extension used to build `φ` as a derivation. -/
abbrev TSd (K : Type) [CommRing K] (T : Type) : Type :=
  TrivSqZeroExt (EAd K T) (EAd K T)

variable {K : Type} [CommRing K] {T : Type} [Fintype T]

/-- `Q̃ : γ ↦ Qγ ∈ Γ₂`, `e ↦ 0`. -/
noncomputable def qmap (Q : Matrix T T K) : Wd K T →ₗ[K] Wd K T :=
  (LinearMap.inr K _ _).comp ((Matrix.mulVecLin Q).comp (LinearMap.fst K _ _))

/-- `w ↦ ι w + ε · ι (Q̃ w)`. -/
noncomputable def Fmap (Q : Matrix T T K) : Wd K T →ₗ[K] TSd K T where
  toFun w := TrivSqZeroExt.inl (ι K w) + TrivSqZeroExt.inr (ι K (qmap Q w))
  map_add' x y := by simp [map_add]; abel
  map_smul' r x := by simp [map_smul]

theorem Fmap_sq (Q : Matrix T T K) (w : Wd K T) : Fmap Q w * Fmap Q w = 0 := by
  apply TrivSqZeroExt.ext
  · simp [Fmap, TrivSqZeroExt.fst_mul]
  · simp [Fmap, TrivSqZeroExt.snd_mul, ExteriorAlgebra.ι_add_mul_swap]

noncomputable def Lift (Q : Matrix T T K) : EAd K T →ₐ[K] TSd K T :=
  ExteriorAlgebra.lift K ⟨Fmap Q, Fmap_sq Q⟩

/-- **The eigenwave operator** `φ`: the even derivation of `⋀(Γ₁ ⊕ Γ₂)` extending `γ ↦ Qγ`,
`e ↦ 0`. -/
noncomputable def phi (Q : Matrix T T K) : EAd K T →+ EAd K T where
  toFun x := (Lift Q x).snd
  map_zero' := by simp
  map_add' x y := by simp [map_add]

theorem lift_fst (Q : Matrix T T K) (x : EAd K T) : (Lift Q x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K (EAd K T) (EAd K T)).comp (Lift Q)
      = AlgHom.id K (EAd K T) := by
    apply ExteriorAlgebra.hom_ext; apply LinearMap.ext; intro w; simp [Lift, Fmap]
  exact congrArg (fun f => f x)
    (congrArg (fun (f : EAd K T →ₐ[K] EAd K T) => (f : EAd K T → EAd K T)) h)

theorem phi_iota (Q : Matrix T T K) (w : Wd K T) : phi Q (ι K w) = ι K (qmap Q w) := by
  simp [phi, Lift, Fmap]

/-- **Leibniz.** -/
theorem phi_mul (Q : Matrix T T K) (x y : EAd K T) :
    phi Q (x * y) = x * phi Q y + phi Q x * y := by
  simp [phi, map_mul, TrivSqZeroExt.snd_mul, lift_fst]

theorem phi_one (Q : Matrix T T K) : phi Q (1 : EAd K T) = 0 := by simp [phi]

/-- A vector of `Γ₁ ⊗ K`. -/
def gamv (v : T → K) : Wd K T := (v, 0)

/-- A vector of `Γ₂ ⊗ K`. -/
def ebv (v : T → K) : Wd K T := (0, v)

/-- `ω⁺ = (a₁ ∧ ⋯ ∧ a_n) ⊗ (b₁ ∧ ⋯ ∧ b_n)`, the `a`'s in `Γ₁` and the `b`'s in `Γ₂`. -/
noncomputable def omegaPlus {n : ℕ} (av bv : Fin n → (T → K)) : EAd K T :=
  (List.ofFn fun k => ι K (gamv (av k))).prod * (List.ofFn fun i => ι K (ebv (bv i))).prod

/-- The general-`n` Weil-type polarisation `Q = [[P, R], [−R, dP]]`.  At `n = 2`, with `P`
symmetric and `R` antisymmetric, this is Zharkov's matrix. -/
def Qweil {n : ℕ} (d : K) (P R : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks P R (-R) (d • P)

/-- `√−d` acting on `Γ₁`: `γ_i ↦ γ_{n+i}`, `γ_{n+i} ↦ −d γ_i`. -/
def J1 {n : ℕ} (d : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 (-(d • (1 : Matrix (Fin n) (Fin n) K))) 1 0

/-- `√−d` acting on `Γ₂`: `e_i ↦ d e_{n+i}`, `e_{n+i} ↦ −e_i`. -/
def J2 {n : ℕ} (d : K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 (-(1 : Matrix (Fin n) (Fin n) K)) (d • 1) 0

/-- `a_k = δ γ_k + γ_{n+k}`, a basis of the `+δ` eigenspace `A ⊂ Γ₁ ⊗ K`. -/
def aWeil {n : ℕ} (δ : K) (k : Fin n) : (Fin n ⊕ Fin n) → K :=
  Sum.elim (δ • Pi.single k 1) (Pi.single k 1)

/-- `b_i = e_i − δ e_{n+i}`, a basis of the `+δ` eigenspace `B ⊂ Γ₂ ⊗ K`. -/
def bWeil {n : ℕ} (δ : K) (i : Fin n) : (Fin n ⊕ Fin n) → K :=
  Sum.elim (Pi.single i 1) ((-δ) • Pi.single i 1)


/-! ### Part 1: the abstract lemma -/

theorem qmap_gamv (Q : Matrix T T K) (v : T → K) : qmap Q (gamv v) = ebv (Q.mulVec v) := by
  simp [qmap, gamv, ebv]

theorem qmap_ebv (Q : Matrix T T K) (v : T → K) : qmap Q (ebv v) = 0 := by
  simp [qmap, ebv]

theorem swap_neg (x y : Wd K T) : ι K x * ι K y = -(ι K y * ι K x) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

/-- `φ` kills a product of vectors that it kills individually. -/
theorem phi_prod_of_zero (Q : Matrix T T K) (l : List (Wd K T)) (h : ∀ x ∈ l, qmap Q x = 0) :
    phi Q (l.map (ι K)).prod = 0 := by
  induction l with
  | nil => simpa using phi_one Q
  | cons x t ih =>
      rw [List.map_cons, List.prod_cons, phi_mul, phi_iota, h x (by simp), map_zero, zero_mul,
          add_zero, ih (fun y hy => h y (by simp [hy])), mul_zero]

/-- Moving a vector past a product of vectors costs one sign per factor. -/
theorem iota_move (x : Wd K T) (l : List (Wd K T)) :
    ι K x * (l.map (ι K)).prod = ((-1 : K) ^ l.length) • ((l.map (ι K)).prod * ι K x) := by
  induction l with
  | nil => simp
  | cons y t ih =>
      rw [List.map_cons, List.prod_cons, ← mul_assoc, swap_neg x y, neg_mul, mul_assoc, ih,
          List.length_cons, pow_succ]
      rw [mul_smul_comm, ← mul_assoc]
      simp

/-- **The `(n+1)`-fold wedge inside an `n`-dimensional space.**  A vector in the span of the
`b`'s annihilates their wedge. -/
theorem iota_span_mul {n : ℕ} (bb : Fin n → Wd K T) (c : Fin n → K) :
    ι K (∑ i, c i • bb i) * (List.ofFn fun i => ι K (bb i)).prod = 0 := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_mul_assoc, ExteriorAlgebra.ι_mul_prod_list bb i, smul_zero]

/-- The lemma, in list form: peel one `a` at a time. -/
theorem phi_wedge (Q : Matrix T T K) {n : ℕ} (bb : Fin n → Wd K T)
    (hb : ∀ i, qmap Q (bb i) = 0)
    (l : List (Wd K T)) (hl : ∀ x ∈ l, ∃ c : Fin n → K, qmap Q x = ∑ i, c i • bb i) :
    phi Q ((l.map (ι K)).prod * (List.ofFn fun i => ι K (bb i)).prod) = 0 := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, one_mul]
      have hh : (List.ofFn fun i => ι K (bb i)) = (List.ofFn bb).map (ι K) := List.map_ofFn.symm
      rw [hh]
      refine phi_prod_of_zero Q _ ?_
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hb i
  | cons x t ih =>
      obtain ⟨c, hc⟩ := hl x (by simp)
      rw [List.map_cons, List.prod_cons, mul_assoc, phi_mul,
          ih (fun y hy => hl y (by simp [hy])), mul_zero, zero_add, phi_iota, hc, ← mul_assoc,
          iota_move, smul_mul_assoc, mul_assoc, iota_span_mul, mul_zero, smul_zero]

theorem ebv_sum {n : ℕ} (c : Fin n → K) (bv : Fin n → (T → K)) :
    ebv (∑ i, c i • bv i) = ∑ i, c i • (ebv (bv i) : Wd K T) := by
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩ <;> simp [ebv, Prod.fst_sum, Prod.snd_sum]

/-- **Part 1.**  If `Q` carries every `a_k` into the span of the `b_i`, the eigenwave kills
`ω⁺`. -/
theorem phi_omegaPlus (Q : Matrix T T K) {n : ℕ} (av bv : Fin n → (T → K))
    (h : ∀ k, ∃ c : Fin n → K, Q.mulVec (av k) = ∑ i, c i • bv i) :
    phi Q (omegaPlus av bv) = 0 := by
  have h1 : (List.ofFn fun k => ι K (gamv (av k)))
      = (List.ofFn (fun k => gamv (av k))).map (ι K) := List.map_ofFn.symm
  rw [omegaPlus, h1]
  refine phi_wedge Q (fun i => ebv (bv i)) (fun i => qmap_ebv Q _) _ ?_
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨c, hc⟩ := h k
  exact ⟨c, by rw [qmap_gamv, hc, ebv_sum]⟩

/-! ### Part 2: the general-`n` Weil-type family -/

/-- **Weil type**: `Q` intertwines the two `CM` actions.  No symmetry of `P` or antisymmetry of
`R` is used. -/
theorem weil_type {n : ℕ} (d : K) (P R : Matrix (Fin n) (Fin n) K) :
    J2 d * Qweil d P R = Qweil d P R * J1 d := by
  simp only [J1, J2, Qweil, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem aWeil_eigen {n : ℕ} (d δ : K) (hd : δ * δ = -d) (k : Fin n) :
    (J1 (n := n) d).mulVec (aWeil δ k) = δ • aWeil (n := n) δ k := by
  funext x
  cases x with
  | inl i =>
      simp only [J1, aWeil, Matrix.fromBlocks_mulVec, Function.comp_apply, Sum.elim_inl,
                 Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
                 Matrix.smul_mulVec, Matrix.one_mulVec, Pi.neg_apply, Pi.smul_apply,
                 smul_eq_mul, Pi.single_apply]
      all_goals (split_ifs with h <;> first | linear_combination hd | linear_combination -hd | ring)
  | inr i =>
      simp only [J1, aWeil, Matrix.fromBlocks_mulVec, Function.comp_apply, Sum.elim_inl,
                 Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
                 Matrix.smul_mulVec, Matrix.one_mulVec, Pi.neg_apply, Pi.smul_apply,
                 smul_eq_mul, Pi.single_apply]
      all_goals (split_ifs with h <;> first | linear_combination hd | linear_combination -hd | ring)

theorem bWeil_eigen {n : ℕ} (d δ : K) (hd : δ * δ = -d) (i : Fin n) :
    (J2 (n := n) d).mulVec (bWeil δ i) = δ • bWeil (n := n) δ i := by
  funext x
  cases x with
  | inl j =>
      simp only [J2, bWeil, Matrix.fromBlocks_mulVec, Function.comp_apply, Sum.elim_inl,
                 Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
                 Matrix.smul_mulVec, Matrix.one_mulVec, Pi.neg_apply, Pi.smul_apply,
                 smul_eq_mul, Pi.single_apply, neg_neg]
      all_goals (split_ifs with h <;> first | linear_combination hd | linear_combination -hd | ring)
  | inr j =>
      simp only [J2, bWeil, Matrix.fromBlocks_mulVec, Function.comp_apply, Sum.elim_inl,
                 Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
                 Matrix.smul_mulVec, Matrix.one_mulVec, Pi.neg_apply, Pi.smul_apply,
                 smul_eq_mul, Pi.single_apply]
      all_goals (split_ifs with h <;> first | linear_combination hd | linear_combination -hd | ring)

/-- **`Q(A) ⊆ B`**, explicitly: `Q a_k = ∑ᵢ (R_{ik} + δ P_{ik}) b_i`. -/
theorem QweilMulVec {n : ℕ} (d δ : K) (hd : δ * δ = -d) (P R : Matrix (Fin n) (Fin n) K)
    (k : Fin n) :
    (Qweil d P R).mulVec (aWeil δ k) = ∑ i : Fin n, (R i k + δ * P i k) • bWeil δ i := by
  funext x
  rw [Finset.sum_apply]
  cases x with
  | inl i =>
      simp [Qweil, aWeil, bWeil, Matrix.fromBlocks_mulVec, Matrix.mulVec_single,
            Matrix.mulVec_smul, Pi.single_apply, Finset.sum_ite_eq]
      ring
  | inr i =>
      simp [Qweil, aWeil, bWeil, Matrix.fromBlocks_mulVec, Matrix.mulVec_single,
            Matrix.mulVec_smul, Matrix.neg_mulVec, Pi.single_apply, Finset.sum_ite_eq, mul_comm]
      linear_combination (P i k) * hd

/-! ### Parts 1 and 2 combined -/

/-- **Lemma B.** -/
theorem proof :
    (∀ (K : Type) [CommRing K] (T : Type) [Fintype T] (Q : Matrix T T K) (n : ℕ)
        (av bv : Fin n → (T → K)),
        (∀ k, ∃ c : Fin n → K, Q.mulVec (av k) = ∑ i, c i • bv i) →
        phi Q (omegaPlus av bv) = 0)
    ∧ (∀ (K : Type) [CommRing K] (n : ℕ) (d δ : K) (P R : Matrix (Fin n) (Fin n) K),
        δ * δ = -d →
          (J2 d * Qweil d P R = Qweil d P R * J1 d)
        ∧ (∀ k : Fin n, (J1 (n := n) d).mulVec (aWeil δ k) = δ • aWeil (n := n) δ k)
        ∧ (∀ i : Fin n, (J2 (n := n) d).mulVec (bWeil δ i) = δ • bWeil (n := n) δ i)
        ∧ (∀ k, (Qweil d P R).mulVec (aWeil δ k)
                  = ∑ i, (R i k + δ * P i k) • bWeil δ i))
    ∧ (∀ (K : Type) [CommRing K] (n : ℕ) (d δ : K) (P R : Matrix (Fin n) (Fin n) K),
        δ * δ = -d → phi (Qweil d P R) (omegaPlus (aWeil δ) (bWeil δ)) = 0) := by
  refine ⟨fun K _ T _ Q n av bv h => phi_omegaPlus Q av bv h, ?_, ?_⟩
  · intro K _ n d δ P R hd
    exact ⟨weil_type d P R, aWeil_eigen d δ hd, bWeil_eigen d δ hd, QweilMulVec d δ hd P R⟩
  · intro K _ n d δ P R hd
    exact phi_omegaPlus _ _ _ fun k => ⟨fun i => R i k + δ * P i k, QweilMulVec d δ hd P R k⟩

end Submissions.EigenwaveKernelWeilOmega.LemmaB
