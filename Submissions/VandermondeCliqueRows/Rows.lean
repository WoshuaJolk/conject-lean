import Mathlib

namespace Submissions.VandermondeCliqueRows.Rows

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

abbrev vand (k : ℕ) (s : ℂ) : Fin k → ℂ := fun r => s ^ (r : ℕ)

abbrev statement : Prop :=
  ∀ (k n : ℕ), 2 ≤ k →
    ∀ t : Fin n → ℂ, Function.Injective t →
      (∀ i j : Fin n,
          pair (vand k (t i)) (vand k (t j)) = 0 ↔
            ((star (t i) * t j) ^ k = 1 ∧ star (t i) * t j ≠ 1)) ∧
      (∀ b : Fin k → Fin n, Function.Injective b →
          LinearIndependent ℂ fun p => vand k (t (b p))) ∧
      (∀ b : Fin (k + 1) → Fin n, Function.Injective b →
          Submodule.span ℂ (Set.range fun p => vand k (t (b p))) = ⊤)

lemma pairing_formula (k : ℕ) (s s' : ℂ) :
    pair (vand k s) (vand k s') =
      ∑ r : Fin k, (star s * s') ^ (r : ℕ) := by
  simp only [pair, vand]
  apply Finset.sum_congr rfl
  intro r hr
  rw [star_pow, mul_pow]

lemma geometric_sum_zero_iff (k : ℕ) (hk : 2 ≤ k) (ρ : ℂ) :
    (∑ r ∈ Finset.range k, ρ ^ r) = 0 ↔
      (ρ ^ k = 1 ∧ ρ ≠ 1) := by
  by_cases hρ : ρ = 1
  · subst ρ
    have hk0 : (k : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hk))
    simp [hk0]
  · have hsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ
    constructor
    · intro hs
      have hfac : (∑ r ∈ Finset.range k, ρ ^ r) * (ρ - 1) =
          ρ ^ k - 1 := geom_sum_mul ρ k
      have hz : ρ ^ k - 1 = 0 := by
        rw [← hfac]
        simp [hs]
      exact ⟨sub_eq_zero.mp hz, hρ⟩
    · rintro ⟨hp, -⟩
      have hfac : (∑ r ∈ Finset.range k, ρ ^ r) * (ρ - 1) =
          ρ ^ k - 1 := geom_sum_mul ρ k
      have hz : (∑ r ∈ Finset.range k, ρ ^ r) * (ρ - 1) = 0 := by
        rw [hfac, hp]
        simp
      exact (mul_eq_zero.mp hz).resolve_right hsub

lemma vandermonde_rows_li {k n : ℕ} (t : Fin n → ℂ)
    (ht : Function.Injective t) (b : Fin k → Fin n)
    (hb : Function.Injective b) :
    LinearIndependent ℂ (fun p => vand k (t (b p))) := by
  let A : Matrix (Fin k) (Fin k) ℂ :=
    fun p q => (t (b p)) ^ (q : ℕ)
  have hnode : Function.Injective (t ∘ b) := ht.comp hb
  have hA : A = Matrix.vandermonde (t ∘ b) := by
    ext p q
    simp [A, Matrix.vandermonde_apply, Function.comp_apply]
  have hdet : A.det ≠ 0 := by
    rw [hA]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnode
  have hrows : LinearIndependent ℂ (fun p => A p) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  simpa [A, vand] using hrows

theorem target : statement := by
  intro k n hk t ht
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [pairing_formula]
    rw [Fin.sum_univ_eq_sum_range]
    rw [geometric_sum_zero_iff k hk (star (t i) * t j)]
  · intro b hb
    exact vandermonde_rows_li t ht b hb
  · intro b hb
    let b₀ : Fin k → Fin (k + 1) := fun p => ⟨p.1, by omega⟩
    have hb₀ : Function.Injective b₀ := by
      intro p q hpq
      apply Fin.ext
      simpa [b₀] using congrArg Fin.val hpq
    have hli : LinearIndependent ℂ
        (fun p => vand k (t (b (b₀ p)))) :=
      vandermonde_rows_li t ht (b ∘ b₀) (hb.comp hb₀)
    letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    have hspan :
        Submodule.span ℂ (Set.range (fun p => vand k (t (b (b₀ p))))) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp)
    have hsub :
        Set.range (fun p => vand k (t (b (b₀ p)))) ⊆
          Set.range (fun p => vand k (t (b p))) := by
      rintro v ⟨p, rfl⟩
      exact ⟨b₀ p, rfl⟩
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono hsub

end
end Submissions.VandermondeCliqueRows.Rows
