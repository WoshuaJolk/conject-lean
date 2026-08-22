import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

/-!
# QubitTwoRegularRigidity — an exactly 2-regular qubit orthogonality graph forces `4 ∣ m`

If `m` nonzero vectors in `C²` have Hermitian orthogonality graph exactly 2-regular
(every vector has exactly two orthogonal partners), then `4 ∣ m`.

Proof shape: in `C²` the orthogonal complement of a nonzero vector is a single complex
line, so a vector's two orthogonal partners are parallel to each other.  Every vector
then has exactly one *parallel* partner among the family besides itself, parallelism
classes have exactly two members, and each pair of parallel classes pairs off into a
`K_{2,2}` (a 4-cycle).  The vertex set thus splits into disjoint 4-element classes
`{i, P i, J i, K i}`, and `m` is 4 times the number of classes.
-/

namespace Submissions.QubitTwoRegularRigidity.QubitRigidity

/-! ### Pure `ℂ` algebra: 2-dimensional linear algebra by hand -/

/-- The Hermitian norm-type sum `star a₀ * a₀ + star a₁ * a₁` vanishes only when both
entries vanish. -/
private lemma comps_eq_zero_of_norm {a0 a1 : ℂ} (h : star a0 * a0 + star a1 * a1 = 0) :
    a0 = 0 ∧ a1 = 0 := by
  have h0 : ((Complex.normSq a0 : ℝ) : ℂ) + ((Complex.normSq a1 : ℝ) : ℂ) = 0 := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact h
  have h1 : Complex.normSq a0 + Complex.normSq a1 = 0 := by
    exact_mod_cast h0
  have h2 := (add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg a0)
    (Complex.normSq_nonneg a1)).mp h1
  exact ⟨Complex.normSq_eq_zero.mp h2.1, Complex.normSq_eq_zero.mp h2.2⟩

/-- Hermitian orthogonality is symmetric. -/
private lemma orth_symm' {a0 a1 b0 b1 : ℂ} (h : star a0 * b0 + star a1 * b1 = 0) :
    star b0 * a0 + star b1 * a1 = 0 := by
  have h2 : star (star a0 * b0 + star a1 * b1) = (0 : ℂ) := by rw [h, star_zero]
  simp only [star_add, star_mul, star_star] at h2
  linear_combination h2

/-- Two vectors annihilated by the same nonzero conjugate functional on `C²` are
parallel. -/
private lemma parallel_of_orth {a0 a1 b0 b1 c0 c1 : ℂ} (ha : ¬(a0 = 0 ∧ a1 = 0))
    (h1 : star a0 * b0 + star a1 * b1 = 0) (h2 : star a0 * c0 + star a1 * c1 = 0) :
    b0 * c1 - b1 * c0 = 0 := by
  have hA : star a0 * (b0 * c1 - b1 * c0) = 0 := by linear_combination c1 * h1 - b1 * h2
  have hB : star a1 * (b0 * c1 - b1 * c0) = 0 := by linear_combination b0 * h2 - c0 * h1
  by_cases h0 : a0 = 0
  · have ha1 : a1 ≠ 0 := fun h' => ha ⟨h0, h'⟩
    exact (mul_eq_zero.mp hB).resolve_left (star_ne_zero.mpr ha1)
  · exact (mul_eq_zero.mp hA).resolve_left (star_ne_zero.mpr h0)

/-- A vector both parallel and orthogonal to a nonzero vector is zero. -/
private lemma zero_of_par_orth {a0 a1 b0 b1 : ℂ} (ha : ¬(a0 = 0 ∧ a1 = 0))
    (hpar : a0 * b1 - a1 * b0 = 0) (horth : star a0 * b0 + star a1 * b1 = 0) :
    b0 = 0 ∧ b1 = 0 := by
  have hN : star a0 * a0 + star a1 * a1 ≠ 0 := fun h => ha (comps_eq_zero_of_norm h)
  have h0 : (star a0 * a0 + star a1 * a1) * b0 = 0 := by
    linear_combination a0 * horth - star a1 * hpar
  have h1 : (star a0 * a0 + star a1 * a1) * b1 = 0 := by
    linear_combination a1 * horth + star a0 * hpar
  exact ⟨(mul_eq_zero.mp h0).resolve_left hN, (mul_eq_zero.mp h1).resolve_left hN⟩

/-- Orthogonality transfers along parallelism: if `b ∥ a` (with `a ≠ 0`) and `a ⊥ l`,
then `b ⊥ l`. -/
private lemma orth_of_par_orth {a0 a1 b0 b1 l0 l1 : ℂ} (ha : ¬(a0 = 0 ∧ a1 = 0))
    (hpar : a0 * b1 - a1 * b0 = 0) (horth : star a0 * l0 + star a1 * l1 = 0) :
    star b0 * l0 + star b1 * l1 = 0 := by
  have hsp : star b1 * star a0 - star b0 * star a1 = 0 := by
    have h := congrArg star hpar
    simp only [star_sub, star_mul, star_zero] at h
    exact h
  have hA : star a0 * (star b0 * l0 + star b1 * l1) = 0 := by
    linear_combination star b0 * horth + l1 * hsp
  have hB : star a1 * (star b0 * l0 + star b1 * l1) = 0 := by
    linear_combination star b1 * horth - l0 * hsp
  by_cases h0 : a0 = 0
  · have ha1 : a1 ≠ 0 := fun h' => ha ⟨h0, h'⟩
    exact (mul_eq_zero.mp hB).resolve_left (star_ne_zero.mpr ha1)
  · exact (mul_eq_zero.mp hA).resolve_left (star_ne_zero.mpr h0)

/-! ### The main theorem -/

theorem proof :
    ∀ m : ℕ, ∀ v : Fin m → Fin 2 → ℂ,
      (∀ i, v i ≠ 0) →
      (∀ i : Fin m, ∃ j k : Fin m,
        j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
        (∑ r, star (v i r) * v j r) = 0 ∧
        (∑ r, star (v i r) * v k r) = 0 ∧
        (∀ l : Fin m, l ≠ i → (∑ r, star (v i r) * v l r) = 0 → (l = j ∨ l = k))) →
      4 ∣ m := by
  intro m v hv hreg
  classical
  -- Nonzero vectors have a nonzero component.
  have hnz : ∀ i : Fin m, ¬(v i 0 = 0 ∧ v i 1 = 0) := by
    intro i ⟨h0, h1⟩
    exact hv i (funext fun r => by fin_cases r <;> assumption)
  -- Expand the Hermitian inner product into components.
  have hsum : ∀ i j : Fin m,
      (∑ r, star (v i r) * v j r) = star (v i 0) * v j 0 + star (v i 1) * v j 1 :=
    fun i j => Fin.sum_univ_two _
  choose J K hJi hKi hJK hoJ0 hoK0 hex0 using hreg
  -- Componentwise orthogonality facts.
  have hoJ : ∀ i, star (v i 0) * v (J i) 0 + star (v i 1) * v (J i) 1 = 0 :=
    fun i => (hsum i (J i)).symm.trans (hoJ0 i)
  have hoK : ∀ i, star (v i 0) * v (K i) 0 + star (v i 1) * v (K i) 1 = 0 :=
    fun i => (hsum i (K i)).symm.trans (hoK0 i)
  have hex : ∀ i l, l ≠ i →
      star (v i 0) * v l 0 + star (v i 1) * v l 1 = 0 → l = J i ∨ l = K i :=
    fun i l hne ho => hex0 i l hne ((hsum i l).trans ho)
  -- Parallelism and orthogonality never coexist among the (nonzero) family members.
  have no_par_orth : ∀ i j : Fin m,
      v i 0 * v j 1 - v i 1 * v j 0 = 0 →
      star (v i 0) * v j 0 + star (v i 1) * v j 1 = 0 → False := by
    intro i j hpar horth
    exact hnz j (zero_of_par_orth (hnz i) hpar horth)
  -- Step A: the two orthogonal partners of `i` are parallel to each other.
  have hparJK : ∀ i, v (J i) 0 * v (K i) 1 - v (J i) 1 * v (K i) 0 = 0 :=
    fun i => parallel_of_orth (hnz i) (hoJ i) (hoK i)
  -- Step B: `i` is one of the two orthogonal partners of `J i` (and of `K i`).
  have hbackJ : ∀ i, i = J (J i) ∨ i = K (J i) :=
    fun i => hex (J i) i (hJi i).symm (orth_symm' (hoJ i))
  have hbackK : ∀ i, i = J (K i) ∨ i = K (K i) :=
    fun i => hex (K i) i (hKi i).symm (orth_symm' (hoK i))
  -- Step C: each `i` has a unique parallel partner `P i ≠ i` in the family.
  have hPex : ∀ i : Fin m, ∃ p, p ≠ i ∧ (v i 0 * v p 1 - v i 1 * v p 0 = 0) ∧
      ∀ q, q ≠ i → v i 0 * v q 1 - v i 1 * v q 0 = 0 → q = p := by
    intro i
    -- Uniqueness core: any two parallel partners of `i` coincide.
    have huniq : ∀ p q, p ≠ i → q ≠ i →
        v i 0 * v p 1 - v i 1 * v p 0 = 0 →
        v i 0 * v q 1 - v i 1 * v q 0 = 0 → p = q := by
      intro p q hp hq hpp hpq
      by_contra hne
      -- `p`, `q`, `i` are three distinct vectors orthogonal to `J i`: impossible.
      have hopJ : star (v p 0) * v (J i) 0 + star (v p 1) * v (J i) 1 = 0 :=
        orth_of_par_orth (hnz i) hpp (hoJ i)
      have hoqJ : star (v q 0) * v (J i) 0 + star (v q 1) * v (J i) 1 = 0 :=
        orth_of_par_orth (hnz i) hpq (hoJ i)
      have hiJ : i ≠ J i := (hJi i).symm
      have hpJ : p ≠ J i := by
        intro h
        exact no_par_orth i (J i) (h ▸ hpp) (hoJ i)
      have hqJ : q ≠ J i := by
        intro h
        exact no_par_orth i (J i) (h ▸ hpq) (hoJ i)
      rcases hex (J i) i hiJ (orth_symm' (hoJ i)) with h1 | h1 <;>
        rcases hex (J i) p hpJ (orth_symm' hopJ) with h2 | h2 <;>
          rcases hex (J i) q hqJ (orth_symm' hoqJ) with h3 | h3 <;>
            first
              | exact hp (h2.trans h1.symm)
              | exact hq (h3.trans h1.symm)
              | exact hne (h2.trans h3.symm)
    -- Existence: the partner of `i` opposite to it inside the partner pair of `J i`.
    rcases hbackJ i with h | h
    · refine ⟨K (J i), ?_, ?_, ?_⟩
      · intro he
        exact hJK (J i) (by rw [← h, he])
      · have hp := hparJK (J i)
        rwa [← h] at hp
      · intro q hq hpq
        refine huniq q (K (J i)) hq ?_ hpq ?_
        · intro he
          exact hJK (J i) (by rw [← h, he])
        · have hp := hparJK (J i)
          rwa [← h] at hp
    · refine ⟨J (J i), ?_, ?_, ?_⟩
      · intro he
        exact hJK (J i) (by rw [he, ← h])
      · -- `par (J (J i)) (K (J i))` with `i = K (J i)` gives `par (J (J i)) i`;
        -- flip to `par i (J (J i))`.
        have hp := hparJK (J i)
        rw [← h] at hp
        linear_combination -hp
      · intro q hq hpq
        refine huniq q (J (J i)) hq ?_ hpq ?_
        · intro he
          exact hJK (J i) (by rw [he, ← h])
        · have hp := hparJK (J i)
          rw [← h] at hp
          linear_combination -hp
  choose P hPne hPpar hPuniq using hPex
  -- P is an involution; the partner maps interlock.
  have hPP : ∀ i, P (P i) = i := by
    intro i
    have h := hPuniq (P i) i (hPne i).symm (by linear_combination -(hPpar i))
    exact h.symm
  have hPJ : ∀ i, P (J i) = K i := by
    intro i
    have h := hPuniq (J i) (K i) (hJK i).symm (hparJK i)
    exact h.symm
  have hPK : ∀ i, P (K i) = J i := by
    intro i
    have h := hPuniq (K i) (J i) (hJK i) (by linear_combination -(hparJK i))
    exact h.symm
  have hPneJ : ∀ i, P i ≠ J i := by
    intro i h
    exact no_par_orth i (J i) (h ▸ hPpar i) (hoJ i)
  have hPneK : ∀ i, P i ≠ K i := by
    intro i h
    exact no_par_orth i (K i) (h ▸ hPpar i) (hoK i)
  -- The partner pair of any orthogonal partner of `i` is `{i, P i}`.
  have hpair : ∀ i w : Fin m, w ≠ i →
      star (v i 0) * v w 0 + star (v i 1) * v w 1 = 0 →
      (J w = i ∧ K w = P i) ∨ (J w = P i ∧ K w = i) := by
    intro i w hw how
    rcases hex w i hw.symm (orth_symm' how) with h | h
    · left
      refine ⟨h.symm, ?_⟩
      have hKne : K w ≠ i := by
        intro he
        exact hJK w (by rw [← h, he])
      have hp := hparJK w
      rw [← h] at hp
      exact hPuniq i (K w) hKne hp
    · right
      refine ⟨?_, h.symm⟩
      have hJne : J w ≠ i := by
        intro he
        exact hJK w (by rw [he, ← h])
      have hp := hparJK w
      rw [← h] at hp
      exact hPuniq i (J w) hJne (by linear_combination -hp)
  -- Parallel vectors have the same partner pair.
  have hJKclass : ∀ i i' : Fin m, i' ≠ i →
      v i 0 * v i' 1 - v i 1 * v i' 0 = 0 →
      (J i' = J i ∧ K i' = K i) ∨ (J i' = K i ∧ K i' = J i) := by
    intro i i' hne hpar
    have hoJ' : star (v i' 0) * v (J i) 0 + star (v i' 1) * v (J i) 1 = 0 :=
      orth_of_par_orth (hnz i) hpar (hoJ i)
    have hoK' : star (v i' 0) * v (K i) 0 + star (v i' 1) * v (K i) 1 = 0 :=
      orth_of_par_orth (hnz i) hpar (hoK i)
    have hJne : J i ≠ i' := by
      intro h
      exact no_par_orth i i' (hpar) ((h ▸ hoJ i : _))
    have hKne : K i ≠ i' := by
      intro h
      exact no_par_orth i i' (hpar) ((h ▸ hoK i : _))
    rcases hex i' (J i) hJne hoJ' with h1 | h1 <;>
      rcases hex i' (K i) hKne hoK' with h2 | h2
    · exact absurd (h1.trans h2.symm) (hJK i)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
    · exact absurd (h1.trans h2.symm) (hJK i)
  -- The 4-element class of `i`.
  have hcard4 : ∀ i, ({i, P i, J i, K i} : Finset (Fin m)).card = 4 := by
    intro i
    have hii : i ∉ ({P i, J i, K i} : Finset (Fin m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hPne i).symm, (hJi i).symm, (hKi i).symm⟩
    have hPii : P i ∉ ({J i, K i} : Finset (Fin m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hPneJ i, hPneK i⟩
    have hJii : J i ∉ ({K i} : Finset (Fin m)) := by
      simp only [Finset.mem_singleton]
      exact hJK i
    rw [Finset.card_insert_of_notMem hii, Finset.card_insert_of_notMem hPii,
      Finset.card_insert_of_notMem hJii, Finset.card_singleton]
  -- Classes are invariant: every member of the class of `i` has the same class.
  have hclass : ∀ i x : Fin m, x ∈ ({i, P i, J i, K i} : Finset (Fin m)) →
      ({x, P x, J x, K x} : Finset (Fin m)) = {i, P i, J i, K i} := by
    intro i x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · -- class of `P i`
      rw [hPP i]
      rcases hJKclass i (P i) (hPne i) (hPpar i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2] <;> (ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    · -- class of `J i`
      rw [hPJ i]
      rcases hpair i (J i) (hJi i) (hoJ i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2] <;> (ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    · -- class of `K i`
      rw [hPK i]
      rcases hpair i (K i) (hKi i) (hoK i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2] <;> (ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  -- Counting: `Fin m` is fibered over the distinct classes, each fiber of size 4.
  have hcount := Finset.card_eq_sum_card_fiberwise
    (f := fun i => ({i, P i, J i, K i} : Finset (Fin m)))
    (s := (Finset.univ : Finset (Fin m)))
    (t := Finset.univ.image (fun i => ({i, P i, J i, K i} : Finset (Fin m))))
    (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
  have hfib : ∀ s ∈ Finset.univ.image (fun i => ({i, P i, J i, K i} : Finset (Fin m))),
      (Finset.univ.filter
        (fun x => ({x, P x, J x, K x} : Finset (Fin m)) = s)).card = 4 := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨i, -, hi⟩
    have hfil : Finset.univ.filter
        (fun x => ({x, P x, J x, K x} : Finset (Fin m)) = s) = s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hfx
        rw [← hfx]
        exact Finset.mem_insert_self x _
      · intro hxs
        rw [← hi] at hxs
        rw [hclass i x hxs, hi]
    rw [hfil, ← hi]
    exact hcard4 i
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hcount
  exact ⟨(Finset.univ.image (fun i => ({i, P i, J i, K i} : Finset (Fin m)))).card,
    hcount.trans (Nat.mul_comm _ 4)⟩

end Submissions.QubitTwoRegularRigidity.QubitRigidity
