import Mathlib

/-!
# `Γ₁` contains no nonzero element of rank at most two

A difference of two rank-one matrices has every `3 × 3` minor zero.  Four particular `3 × 3`
minors of `∑ nᵢ γᵢ` are `n₀(n₀² + d n₂²)`, `-d n₂(n₀² + d n₂²)`, `-n₁(n₁² + d n₃²)` and
`d n₃(n₁² + d n₃²)`; with `d > 0` these force `n = 0`.
-/

namespace Submissions.GammaOneRankOne.RankOne

noncomputable section

abbrev G2 : Type := Fin 4 → ℤ
abbrev Gp : Type := Fin 4 → ℤ
abbrev G2P : Type := Fin 4 → Fin 4 → ℤ

def outer (u : G2) (s : Gp) : G2P := fun i k => u i * s k

def gammaGen (d : ℤ) : Fin 4 → G2P :=
  ![ ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]],
     ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, -1], ![d, 0, 0, 0], ![0, d, 0, 0]],
     ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, d, 0, 0], ![0, 0, d, 0]] ]

noncomputable def gammaOne (d : ℤ) : Submodule ℤ G2P :=
  Submodule.span ℤ (Set.range (gammaGen d))

/-- The `3 × 3` minor of a matrix given by its nine entries. -/
def minor3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℤ) : ℤ :=
  a11 * (a22 * a33 - a23 * a32) - a12 * (a21 * a33 - a23 * a31)
    + a13 * (a21 * a32 - a22 * a31)

/-- Every `3 × 3` minor of a difference of two rank-one matrices vanishes. -/
lemma minor3_rank_two (u v : G2) (s t : Gp) (j1 j2 j3 m1 m2 m3 : Fin 4) :
    minor3 (u j1 * s m1 - v j1 * t m1) (u j1 * s m2 - v j1 * t m2) (u j1 * s m3 - v j1 * t m3)
           (u j2 * s m1 - v j2 * t m1) (u j2 * s m2 - v j2 * t m2) (u j2 * s m3 - v j2 * t m3)
           (u j3 * s m1 - v j3 * t m1) (u j3 * s m2 - v j3 * t m2) (u j3 * s m3 - v j3 * t m3)
      = 0 := by
  simp only [minor3]; ring

lemma sq_add_eq_zero {p q dd : ℤ} (hd : 0 < dd) (h : p ^ 2 + dd * q ^ 2 = 0) :
    p = 0 ∧ q = 0 := by
  have h1 : 0 ≤ p ^ 2 := sq_nonneg p
  have h2 : 0 ≤ dd * q ^ 2 := mul_nonneg hd.le (sq_nonneg q)
  have hp : p ^ 2 = 0 := by omega
  have hq : dd * q ^ 2 = 0 := by omega
  have hq2 : q ^ 2 = 0 := by
    rcases mul_eq_zero.1 hq with h' | h'
    · omega
    · exact h'
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hp,
         pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hq2⟩

theorem proof :
    ∀ (d : ℤ), 0 < d → ∀ (u v : G2) (s t : Gp),
      outer u s - outer v t ∈ gammaOne d → outer u s = outer v t := by
  intro d hd u v s t hmem
  rw [gammaOne, Submodule.mem_span_range_iff_exists_fun ℤ] at hmem
  obtain ⟨n, hn⟩ := hmem
  -- entrywise form
  have hval : ∀ j m : Fin 4,
      u j * s m - v j * t m = ∑ i : Fin 4, n i * gammaGen d i j m := by
    intro j m
    have := congrFun (congrFun hn j) m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, outer] at this
    exact this.symm
  -- the four minors
  have A := minor3_rank_two u v s t 0 1 3 0 1 3
  have B := minor3_rank_two u v s t 1 2 3 0 1 3
  have C := minor3_rank_two u v s t 0 1 2 1 2 3
  have D := minor3_rank_two u v s t 0 2 3 1 2 3
  simp only [hval, minor3, gammaGen, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four] at A B C D
  -- A : n0 * (n0^2 + d n2^2) = 0 ;  B : -d n2 * (...) = 0 ; similarly C, D
  have hP : (n 0) ^ 2 + d * (n 2) ^ 2 = 0 := by
    by_contra hne
    have hPpos : 0 < (n 0) ^ 2 + d * (n 2) ^ 2 := by
      have h1 : 0 ≤ (n 0) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ d * (n 2) ^ 2 := mul_nonneg hd.le (sq_nonneg _)
      omega
    have hn0 : n 0 = 0 := by
      rcases mul_eq_zero.1 (by linarith [A] : (n 0) * ((n 0) ^ 2 + d * (n 2) ^ 2) = 0) with h | h
      · exact h
      · exact absurd h (by omega)
    have hn2 : n 2 = 0 := by
      have hB' : d * (n 2) * ((n 0) ^ 2 + d * (n 2) ^ 2) = 0 := by linarith [B]
      rcases mul_eq_zero.1 hB' with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · omega
        · exact h'
      · exact absurd h (by omega)
    rw [hn0, hn2] at hPpos; simp at hPpos
  have hQ : (n 1) ^ 2 + d * (n 3) ^ 2 = 0 := by
    by_contra hne
    have hQpos : 0 < (n 1) ^ 2 + d * (n 3) ^ 2 := by
      have h1 : 0 ≤ (n 1) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ d * (n 3) ^ 2 := mul_nonneg hd.le (sq_nonneg _)
      omega
    have hn1 : n 1 = 0 := by
      rcases mul_eq_zero.1 (by linarith [C] : (n 1) * ((n 1) ^ 2 + d * (n 3) ^ 2) = 0) with h | h
      · exact h
      · exact absurd h (by omega)
    have hn3 : n 3 = 0 := by
      have hD' : d * (n 3) * ((n 1) ^ 2 + d * (n 3) ^ 2) = 0 := by linarith [D]
      rcases mul_eq_zero.1 hD' with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · omega
        · exact h'
      · exact absurd h (by omega)
    rw [hn1, hn3] at hQpos; simp at hQpos
  obtain ⟨h0, h2⟩ := sq_add_eq_zero hd hP
  obtain ⟨h1, h3⟩ := sq_add_eq_zero hd hQ
  have hzero : ∑ i : Fin 4, n i • gammaGen d i = 0 := by
    rw [Fin.sum_univ_four, h0, h1, h2, h3]
    simp
  rw [hzero] at hn
  funext j m
  have := congrFun (congrFun hn.symm j) m
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

end

end Submissions.GammaOneRankOne.RankOne
