/-
Submission for `Statements.GadgetSeedFromFour`.

For every `k ≥ 4` there is a `k × k` complex matrix with zero diagonal, no zero entry off the
diagonal, and pairwise orthogonal rows of common squared norm `k²`.

Construction (circulant): let `ω = exp(2πi/k)` and let `λ : ℕ → ℂ` be unimodular with zero sum.
Set `M i j = ∑ t, λ t * ω^((i-j)t)`.  Character orthogonality gives
`⟪M i, M j⟫ = k² [i = j]` for free; the diagonal is `∑ λ`, and the off-diagonal entries are the
"Fourier coefficients" `F(d) = ∑ t, λ t ω^(dt)` for `k ∤ d`.  We take pair-cancelling `λ`
(with a cube-root triple in front when `k` is odd) driven by one free unimodular phase `z`; then
`F(d)` is the evaluation at `z` of an explicit nonzero polynomial, and a `z` on the (infinite)
unit circle avoiding the finitely many roots of the product polynomial does the job.
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace Submissions.GadgetSeedFromFour.GadgetSeed

open Complex Polynomial Finset

noncomputable section

/-- The Hermitian pairing of two rows, conjugate-linear in the first argument. -/
abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-! ### Generalities on unimodular numbers and the unit circle -/

lemma star_exp_mul_self {x : ℂ} (hx : (starRingEnd ℂ) x = -x) :
    star (Complex.exp x) * Complex.exp x = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, hx, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero]

lemma conj_two_pi_I_div (n : ℕ) :
    (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
      = -(2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := by
  rw [map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_natCast]
  ring

/-- The set of unimodular complex numbers is infinite. -/
lemma unimodular_infinite : {z : ℂ | star z * z = 1}.Infinite := by
  have key : ∀ x : ℝ, ((x : ℂ) + Complex.I) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp at hi
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
    intro x
    rw [map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hconj0 : ∀ x : ℝ, (starRingEnd ℂ) ((x : ℂ) + Complex.I) ≠ 0 := by
    intro x h
    rw [hconj] at h
    have hi := congrArg Complex.im h
    simp at hi
  refine Set.infinite_of_injective_forall_mem
    (f := fun x : ℝ => (starRingEnd ℂ) ((x : ℂ) + Complex.I) / ((x : ℂ) + Complex.I)) ?_ ?_
  · intro x y h
    simp only at h
    rw [div_eq_div_iff (key x) (key y), hconj, hconj] at h
    have hxy : ((x : ℂ) - y) = 0 := by
      have h2 : (2 : ℂ) * Complex.I * ((x : ℂ) - y) = 0 := by linear_combination h
      have h3 : ((2 : ℂ) * Complex.I) ≠ 0 := by
        simp [Complex.I_ne_zero]
      exact (mul_eq_zero.mp h2).resolve_left h3
    exact_mod_cast sub_eq_zero.mp hxy
  · intro x
    show (starRingEnd ℂ) _ / _ ∈ {z : ℂ | star z * z = 1}
    simp only [Set.mem_ofPred_eq, Complex.star_def]
    rw [map_div₀, Complex.conj_conj, div_mul_div_comm,
      mul_comm ((starRingEnd ℂ) ((x : ℂ) + Complex.I)) ((x : ℂ) + Complex.I)]
    exact div_self (mul_ne_zero (key x) (hconj0 x))

/-! ### Character orthogonality -/

lemma charSum {k : ℕ} (hk : k ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω k) (m : ℤ) :
    (∑ r : Fin k, ω ^ (((r : ℕ) : ℤ) * m)) = if (k : ℤ) ∣ m then (k : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hk
  have hpow : ∀ r : Fin k, ω ^ (((r : ℕ) : ℤ) * m) = (ω ^ m) ^ (r : ℕ) := by
    intro r
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp only [hpow]
  rw [Fin.sum_univ_eq_sum_range (fun n => (ω ^ m) ^ n) k]
  by_cases hd : (k : ℤ) ∣ m
  · rw [if_pos hd, (hω.zpow_eq_one_iff_dvd m).mpr hd]
    simp
  · rw [if_neg hd]
    have h1 : ω ^ m ≠ 1 := fun h => hd ((hω.zpow_eq_one_iff_dvd m).mp h)
    rw [geom_sum_eq h1]
    have hk1 : (ω ^ m) ^ k = 1 := by
      rw [← zpow_natCast (ω ^ m) k, ← zpow_mul, mul_comm m ((k : ℕ) : ℤ), zpow_mul,
        hω.zpow_eq_one, one_zpow]
    rw [hk1, sub_self, zero_div]

lemma dvd_sub_iff {k : ℕ} {i j : Fin k} :
    (k : ℤ) ∣ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ↔ i = j := by
  constructor
  · intro h
    have hi : ((i : ℕ) : ℤ) < k := by exact_mod_cast i.isLt
    have hj : ((j : ℕ) : ℤ) < k := by exact_mod_cast j.isLt
    have h0 : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 0 :=
      Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; omega)
    have hij : (i : ℕ) = (j : ℕ) := by omega
    exact Fin.ext hij
  · rintro rfl
    simp

/-! ### The pairing computation: orthogonality is free for unimodular symbols -/

lemma pairing {k : ℕ} (hk : k ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω k) (hsω : star ω = ω⁻¹)
    (lam : Fin k → ℂ) (hlam : ∀ t, star (lam t) * lam t = 1) (i j : Fin k) :
    pair (fun r : Fin k => ∑ t : Fin k, lam t * ω ^ ((((i : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ)))
      (fun r : Fin k => ∑ t : Fin k, lam t * ω ^ ((((j : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ)))
      = if i = j then ((k : ℂ)) ^ 2 else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hk
  have hstar : ∀ n : ℤ, star (ω ^ n) = ω ^ (-n) := by
    intro n
    rw [star_zpow₀, hsω, inv_zpow']
  have hmul : ∀ a b : ℤ, ω ^ a * ω ^ b = ω ^ (a + b) := fun a b => (zpow_add₀ hω0 a b).symm
  have key : (∑ r : Fin k,
      star (∑ t : Fin k, lam t * ω ^ ((((i : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ))) *
        (∑ t : Fin k, lam t * ω ^ ((((j : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ))))
      = if i = j then ((k : ℂ)) ^ 2 else 0 := by
    calc (∑ r : Fin k,
        star (∑ t : Fin k, lam t * ω ^ ((((i : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ))) *
          (∑ t : Fin k, lam t * ω ^ ((((j : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ))))
        = ∑ r : Fin k, ∑ t : Fin k, ∑ s : Fin k,
            (star (lam t) * ω ^ (-((((i : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ)))) *
              (lam s * ω ^ ((((j : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((s : ℕ) : ℤ))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
          rw [star_mul', hstar]
      _ = ∑ t : Fin k, ∑ s : Fin k, ∑ r : Fin k,
            (star (lam t) * ω ^ (-((((i : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ)))) *
              (lam s * ω ^ ((((j : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((s : ℕ) : ℤ))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ t : Fin k, ∑ s : Fin k,
            (star (lam t) * lam s *
                ω ^ (((j : ℕ) : ℤ) * ((s : ℕ) : ℤ) - ((i : ℕ) : ℤ) * ((t : ℕ) : ℤ))) *
              (if (k : ℤ) ∣ (((t : ℕ) : ℤ) - ((s : ℕ) : ℤ)) then (k : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
          rw [← charSum hk hω (((t : ℕ) : ℤ) - ((s : ℕ) : ℤ)), Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hx : ω ^ (-((((i : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((t : ℕ) : ℤ))) *
                ω ^ ((((j : ℕ) : ℤ) - ((r : ℕ) : ℤ)) * ((s : ℕ) : ℤ))
              = ω ^ (((j : ℕ) : ℤ) * ((s : ℕ) : ℤ) - ((i : ℕ) : ℤ) * ((t : ℕ) : ℤ)) *
                ω ^ (((r : ℕ) : ℤ) * (((t : ℕ) : ℤ) - ((s : ℕ) : ℤ))) := by
            rw [hmul, hmul]
            exact congrArg (ω ^ ·) (by ring)
          linear_combination (star (lam t) * lam s) * hx
      _ = ∑ t : Fin k,
            (star (lam t) * lam t *
                ω ^ (((j : ℕ) : ℤ) * ((t : ℕ) : ℤ) - ((i : ℕ) : ℤ) * ((t : ℕ) : ℤ))) * (k : ℂ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          have hs0 : ∀ s : Fin k, s ∈ Finset.univ → s ≠ t →
              (star (lam t) * lam s *
                  ω ^ (((j : ℕ) : ℤ) * ((s : ℕ) : ℤ) - ((i : ℕ) : ℤ) * ((t : ℕ) : ℤ))) *
                (if (k : ℤ) ∣ (((t : ℕ) : ℤ) - ((s : ℕ) : ℤ)) then (k : ℂ) else 0) = 0 := by
            intro s _ hs
            rw [if_neg (fun hdvd => hs (dvd_sub_iff.mp hdvd).symm), mul_zero]
          rw [Finset.sum_eq_single t hs0 (fun h => absurd (Finset.mem_univ t) h),
            if_pos (by simp)]
      _ = (k : ℂ) * ∑ t : Fin k, ω ^ (((t : ℕ) : ℤ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hlam t, one_mul, mul_comm]
          congr 1
          exact congrArg (ω ^ ·) (by ring)
      _ = (k : ℂ) * (if (k : ℤ) ∣ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) then (k : ℂ) else 0) := by
          rw [charSum hk hω]
      _ = if i = j then ((k : ℂ)) ^ 2 else 0 := by
          by_cases hij : i = j
          · subst hij
            rw [if_pos (by simp), if_pos rfl, sq]
          · rw [if_neg (fun hdvd => hij ((dvd_sub_iff.mp hdvd).symm)), if_neg hij, mul_zero]
  exact key

/-! ### Splitting sums into consecutive pairs -/

lemma sum_range_add' (g : ℕ → ℂ) (m n : ℕ) :
    ∑ t ∈ Finset.range (m + n), g t
      = (∑ t ∈ Finset.range m, g t) + ∑ t ∈ Finset.range n, g (m + t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

lemma sum_pairs (g : ℕ → ℂ) (a : ℕ) :
    ∑ t ∈ Finset.range (2 * a), g t = ∑ p ∈ Finset.range a, (g (2 * p) + g (2 * p + 1)) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n) + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

/-! ### The symbol `λ`: even case -/

/-- Even case symbol: `λ (2p) = z^p`, `λ (2p+1) = -z^p`. -/
def lamE (z : ℂ) (t : ℕ) : ℂ := (-1) ^ t * z ^ (t / 2)

lemma lamE_pair (u z : ℂ) (p : ℕ) :
    lamE z (2 * p) * u ^ (2 * p) + lamE z (2 * p + 1) * u ^ (2 * p + 1)
      = (1 - u) * (u ^ (2 * p) * z ^ p) := by
  unfold lamE
  have h1 : (2 * p) / 2 = p := by omega
  have h2 : (2 * p + 1) / 2 = p := by omega
  rw [h1, h2]
  have h3 : (-1 : ℂ) ^ (2 * p) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  have h4 : (-1 : ℂ) ^ (2 * p + 1) = -1 := by rw [pow_succ, h3, one_mul]
  rw [h3, h4, pow_succ]
  ring

lemma lamE_sum (u z : ℂ) (a : ℕ) :
    ∑ t ∈ Finset.range (2 * a), lamE z t * u ^ t
      = (1 - u) * ∑ p ∈ Finset.range a, u ^ (2 * p) * z ^ p := by
  rw [sum_pairs (fun t => lamE z t * u ^ t) a, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => lamE_pair u z p

lemma lamE_diag (z : ℂ) (a : ℕ) : ∑ t ∈ Finset.range (2 * a), lamE z t = 0 := by
  have h := lamE_sum 1 z a
  simp only [one_pow, mul_one, one_mul] at h
  rw [h, sub_self, zero_mul]

lemma lamE_unit {z : ℂ} (hz : star z * z = 1) (t : ℕ) : star (lamE z t) * lamE z t = 1 := by
  unfold lamE
  rw [star_mul', star_pow, star_pow]
  have hs1 : star (-1 : ℂ) = -1 := by simp
  rw [hs1]
  have h2 : ((-1 : ℂ)) ^ t * ((-1 : ℂ)) ^ t = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have h3 : (star z) ^ (t / 2) * z ^ (t / 2) = 1 := by rw [← mul_pow, hz, one_pow]
  calc (-1 : ℂ) ^ t * (star z) ^ (t / 2) * ((-1 : ℂ) ^ t * z ^ (t / 2))
      = ((-1 : ℂ) ^ t * (-1 : ℂ) ^ t) * ((star z) ^ (t / 2) * z ^ (t / 2)) := by ring
    _ = 1 := by rw [h2, h3, one_mul]

/-! ### The symbol `λ`: odd case -/

/-- Odd case symbol: `1, ζ, ζ²` in front, then `λ (3+2p) = z^(p+1)`, `λ (4+2p) = -z^(p+1)`. -/
def lamO (ζ z : ℂ) (t : ℕ) : ℂ :=
  if t < 3 then ζ ^ t else (-1) ^ (t + 1) * z ^ ((t - 1) / 2)

lemma lamO_shift (ζ z : ℂ) (t : ℕ) : lamO ζ z (3 + t) = z * lamE z t := by
  unfold lamO lamE
  rw [if_neg (by omega)]
  have h1 : (3 + t - 1) / 2 = t / 2 + 1 := by omega
  have h2 : (-1 : ℂ) ^ (3 + t + 1) = (-1) ^ t := by
    rw [show 3 + t + 1 = t + 4 by omega, pow_add]
    norm_num
  rw [h1, h2, pow_succ]
  ring

lemma lamO_sum (ζ u z : ℂ) (a : ℕ) :
    ∑ t ∈ Finset.range (2 * a + 3), lamO ζ z t * u ^ t
      = (1 + ζ * u + ζ ^ 2 * u ^ 2)
          + u ^ 3 * (z * ((1 - u) * ∑ p ∈ Finset.range a, u ^ (2 * p) * z ^ p)) := by
  rw [show 2 * a + 3 = 3 + 2 * a by omega,
    sum_range_add' (fun t => lamO ζ z t * u ^ t) 3 (2 * a)]
  congr 1
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    have h0 : lamO ζ z 0 = 1 := by simp [lamO]
    have h1 : lamO ζ z 1 = ζ := by simp [lamO]
    have h2 : lamO ζ z 2 = ζ ^ 2 := by simp [lamO]
    rw [h0, h1, h2]
    ring
  · have hterm : ∀ t : ℕ, lamO ζ z (3 + t) * u ^ (3 + t) = u ^ 3 * (z * (lamE z t * u ^ t)) := by
      intro t
      rw [lamO_shift, pow_add]
      ring
    calc ∑ t ∈ Finset.range (2 * a), lamO ζ z (3 + t) * u ^ (3 + t)
        = ∑ t ∈ Finset.range (2 * a), u ^ 3 * (z * (lamE z t * u ^ t)) :=
          Finset.sum_congr rfl fun t _ => hterm t
      _ = u ^ 3 * (z * ((1 - u) * ∑ p ∈ Finset.range a, u ^ (2 * p) * z ^ p)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, lamE_sum]

lemma zeta_sum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : 1 + ζ + ζ ^ 2 = 0 := by
  have h3 : ζ ^ (3 : ℕ) = 1 := hζ.pow_eq_one
  have hne : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have h := geom_sum_eq hne 3
  rw [h3, sub_self, zero_div] at h
  calc 1 + ζ + ζ ^ 2 = ∑ i ∈ Finset.range 3, ζ ^ i := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
        ring
    _ = 0 := h

lemma lamO_diag {ζ : ℂ} (hζs : 1 + ζ + ζ ^ 2 = 0) (z : ℂ) (a : ℕ) :
    ∑ t ∈ Finset.range (2 * a + 3), lamO ζ z t = 0 := by
  have h := lamO_sum ζ 1 z a
  simp only [one_pow, mul_one, one_mul] at h
  rw [h, hζs, sub_self, zero_mul, mul_zero, zero_add]

lemma lamO_unit {ζ z : ℂ} (hζu : star ζ * ζ = 1) (hz : star z * z = 1) (t : ℕ) :
    star (lamO ζ z t) * lamO ζ z t = 1 := by
  unfold lamO
  by_cases h : t < 3
  · rw [if_pos h, star_pow, ← mul_pow, hζu, one_pow]
  · rw [if_neg h, star_mul', star_pow, star_pow]
    have hs1 : star (-1 : ℂ) = -1 := by simp
    rw [hs1]
    have h2 : ((-1 : ℂ)) ^ (t + 1) * ((-1 : ℂ)) ^ (t + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have h3 : (star z) ^ ((t - 1) / 2) * z ^ ((t - 1) / 2) = 1 := by
      rw [← mul_pow, hz, one_pow]
    calc (-1 : ℂ) ^ (t + 1) * (star z) ^ ((t - 1) / 2) *
          ((-1 : ℂ) ^ (t + 1) * z ^ ((t - 1) / 2))
        = ((-1 : ℂ) ^ (t + 1) * (-1 : ℂ) ^ (t + 1)) *
            ((star z) ^ ((t - 1) / 2) * z ^ ((t - 1) / 2)) := by ring
      _ = 1 := by rw [h2, h3, one_mul]

/-! ### The polynomials whose evaluations are the Fourier coefficients -/

/-- `(1-u) * ∑_{p<a} u^{2p} X^p`; its evaluation at `z` is the even-case Fourier coefficient. -/
def geomPoly (a : ℕ) (u : ℂ) : Polynomial ℂ :=
  C (1 - u) * ∑ p ∈ Finset.range a, C (u ^ (2 * p)) * X ^ p

lemma geomPoly_eval (a : ℕ) (u z : ℂ) :
    (geomPoly a u).eval z = (1 - u) * ∑ p ∈ Finset.range a, u ^ (2 * p) * z ^ p := by
  unfold geomPoly
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma geomPoly_coeff (m : ℕ) (u : ℂ) :
    (geomPoly (m + 1) u).coeff m = (1 - u) * u ^ (2 * m) := by
  unfold geomPoly
  rw [Polynomial.coeff_C_mul]
  congr 1
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro p _ hp
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hp h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma geomPoly_ne_zero {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (m : ℕ) :
    geomPoly (m + 1) u ≠ 0 := by
  intro h
  have hc := geomPoly_coeff m u
  rw [h, Polynomial.coeff_zero] at hc
  exact (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu1)) (pow_ne_zero _ hu0)) hc.symm

/-- The odd-case polynomial: constant `1 + ζu + ζ²u²` plus `u³ X ⬝ geomPoly`. -/
def oddPoly (a : ℕ) (ζ u : ℂ) : Polynomial ℂ :=
  C (1 + ζ * u + ζ ^ 2 * u ^ 2) + C (u ^ 3) * (X * geomPoly a u)

lemma oddPoly_eval (a : ℕ) (ζ u z : ℂ) :
    (oddPoly a ζ u).eval z
      = (1 + ζ * u + ζ ^ 2 * u ^ 2)
          + u ^ 3 * (z * ((1 - u) * ∑ p ∈ Finset.range a, u ^ (2 * p) * z ^ p)) := by
  unfold oddPoly
  rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, geomPoly_eval]

lemma oddPoly_ne_zero (ζ : ℂ) {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (m : ℕ) :
    oddPoly (m + 1) ζ u ≠ 0 := by
  intro h
  have hc : (oddPoly (m + 1) ζ u).coeff (m + 1) = u ^ 3 * ((1 - u) * u ^ (2 * m)) := by
    unfold oddPoly
    rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.succ_ne_zero m), zero_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, geomPoly_coeff]
  rw [h, Polynomial.coeff_zero] at hc
  exact (mul_ne_zero (pow_ne_zero _ hu0)
    (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu1)) (pow_ne_zero _ hu0))) hc.symm

/-! ### The main construction -/

lemma build (k : ℕ) (hk4 : 4 ≤ k) {ω : ℂ} (hω : IsPrimitiveRoot ω k) (hωu : star ω * ω = 1)
    (lam : ℂ → ℕ → ℂ) (P : ℂ → Polynomial ℂ)
    (hunit : ∀ z : ℂ, star z * z = 1 → ∀ t : ℕ, star (lam z t) * lam z t = 1)
    (hdiag : ∀ z : ℂ, ∑ t ∈ Finset.range k, lam z t = 0)
    (hP0 : ∀ u : ℂ, u ≠ 0 → u ≠ 1 → P u ≠ 0)
    (heval : ∀ u z : ℂ, ∑ t ∈ Finset.range k, lam z t * u ^ t = (P u).eval z) :
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0) := by
  have hk : k ≠ 0 := by omega
  have hω0 : ω ≠ 0 := hω.ne_zero hk
  have hsω : star ω = ω⁻¹ := eq_inv_of_mul_eq_one_left hωu
  set Q : Polynomial ℂ := ∏ ij : Fin k × Fin k,
      (if ij.1 = ij.2 then 1 else P (ω ^ (((ij.1 : ℕ) : ℤ) - ((ij.2 : ℕ) : ℤ)))) with hQdef
  have hu1 : ∀ i j : Fin k, i ≠ j → ω ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ≠ 1 := by
    intro i j hij h1
    exact hij (dvd_sub_iff.mp ((hω.zpow_eq_one_iff_dvd _).mp h1))
  have hQ0 : Q ≠ 0 := by
    rw [hQdef, Finset.prod_ne_zero_iff]
    intro ij _
    by_cases hd : ij.1 = ij.2
    · rw [if_pos hd]
      exact one_ne_zero
    · rw [if_neg hd]
      exact hP0 _ (zpow_ne_zero _ hω0) (hu1 ij.1 ij.2 hd)
  obtain ⟨z, hzu, hzQ⟩ : ∃ z : ℂ, star z * z = 1 ∧ ¬ Q.IsRoot z := by
    obtain ⟨z, hz⟩ := (unimodular_infinite.sdiff (Polynomial.finite_setOfPred_isRoot hQ0)).nonempty
    exact ⟨z, hz.1, hz.2⟩
  have hfac : ∀ i j : Fin k, i ≠ j → (P (ω ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))).eval z ≠ 0 := by
    intro i j hij hzero
    apply hzQ
    show Q.eval z = 0
    rw [hQdef, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (i, j)) ?_
    rw [if_neg hij]
    exact hzero
  have hM : ∀ i j : Fin k,
      (∑ t : Fin k, lam z t * ω ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((t : ℕ) : ℤ)))
        = (P (ω ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)))).eval z := by
    intro i j
    rw [← heval (ω ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) z,
      ← Fin.sum_univ_eq_sum_range
        (fun t => lam z t * (ω ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) ^ t) k]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [zpow_mul, zpow_natCast]
  refine ⟨fun i j => ∑ t : Fin k, lam z t * ω ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((t : ℕ) : ℤ)),
    (k : ℂ) ^ 2, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr hk)
  · intro i
    show (∑ t : Fin k, lam z t * ω ^ ((((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) * ((t : ℕ) : ℤ))) = 0
    have h1 : ∀ t : Fin k, ω ^ ((((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) * ((t : ℕ) : ℤ)) = 1 := by
      intro t
      rw [sub_self, zero_mul, zpow_zero]
    calc ∑ t : Fin k, lam z t * ω ^ ((((i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) * ((t : ℕ) : ℤ))
        = ∑ t : Fin k, lam z t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [h1 t, mul_one]
      _ = ∑ t ∈ Finset.range k, lam z t := Fin.sum_univ_eq_sum_range (fun t => lam z t) k
      _ = 0 := hdiag z
  · intro i j hij
    show (∑ t : Fin k, lam z t * ω ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((t : ℕ) : ℤ))) ≠ 0
    rw [hM i j]
    exact hfac i j hij
  · intro i j
    exact pairing hk hω hsω (fun t => lam z t) (fun t => hunit z hzu t) i j

/-! ### The two parity cases -/

lemma even_case (k : ℕ) (hk4 : 4 ≤ k) {ω : ℂ} (hω : IsPrimitiveRoot ω k)
    (hωu : star ω * ω = 1) (a : ℕ) (ha : k = 2 * a) (ha2 : 2 ≤ a) :
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0) := by
  refine build k hk4 hω hωu lamE (geomPoly a) ?_ ?_ ?_ ?_
  · exact fun z hz t => lamE_unit hz t
  · intro z
    rw [ha]
    exact lamE_diag z a
  · intro u hu0 hu1
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    exact geomPoly_ne_zero hu0 hu1 m
  · intro u z
    rw [ha, lamE_sum, geomPoly_eval]

lemma odd_case (k : ℕ) (hk4 : 4 ≤ k) {ω : ℂ} (hω : IsPrimitiveRoot ω k)
    (hωu : star ω * ω = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (hζu : star ζ * ζ = 1)
    (a : ℕ) (ha : k = 2 * a + 3) (ha1 : 1 ≤ a) :
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0) := by
  have hζs : 1 + ζ + ζ ^ 2 = 0 := zeta_sum hζ
  refine build k hk4 hω hωu (lamO ζ) (oddPoly a ζ) ?_ ?_ ?_ ?_
  · exact fun z hz t => lamO_unit hζu hz t
  · intro z
    rw [ha]
    exact lamO_diag hζs z a
  · intro u hu0 hu1
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    exact oddPoly_ne_zero ζ hu0 hu1 m
  · intro u z
    rw [ha, lamO_sum, oddPoly_eval]

/-! ### The theorem -/

theorem proof : ∀ k : ℕ, 4 ≤ k →
    ∃ (M : Fin k → Fin k → ℂ) (c : ℂ), c ≠ 0 ∧
      (∀ i, M i i = 0) ∧
      (∀ i j, i ≠ j → M i j ≠ 0) ∧
      (∀ i j, pair (M i) (M j) = if i = j then c else 0) := by
  intro k hk4
  have hk : k ≠ 0 := by omega
  obtain ⟨ω, hω, hωu⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω k ∧ star ω * ω = 1 :=
    ⟨_, Complex.isPrimitiveRoot_exp k hk, star_exp_mul_self (conj_two_pi_I_div k)⟩
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨a, ha⟩ := he
    exact even_case k hk4 hω hωu a (by omega) (by omega)
  · obtain ⟨b, hb⟩ := ho
    obtain ⟨ζ, hζ, hζu⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 ∧ star ζ * ζ = 1 :=
      ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num), star_exp_mul_self (conj_two_pi_I_div 3)⟩
    exact odd_case k hk4 hω hωu hζ hζu (b - 1) (by omega) (by omega)

end

end Submissions.GadgetSeedFromFour.GadgetSeed
