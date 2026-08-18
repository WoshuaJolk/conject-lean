import Commons.PaleyLocalizationTheta
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace Submissions.PaleyLocRegular.CharacterCount



variable {p : ℕ} [Fact (Nat.Prime p)]

/-- the quadratic character of `ZMod p`, as a real number -/
noncomputable def chi (p : ℕ) [Fact (Nat.Prime p)] (z : ZMod p) : ℝ :=
  ((quadraticChar (ZMod p) z : ℤ) : ℝ)

lemma chi_zero : chi p 0 = 0 := by simp [chi]

lemma chi_mul (a b : ZMod p) : chi p (a * b) = chi p a * chi p b := by
  simp [chi, map_mul]

lemma chi_sum_zero (hp2 : p ≠ 2) : ∑ a : ZMod p, chi p a = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2
  have := quadraticChar_sum_zero (F := ZMod p) hF
  simp only [chi]
  rw [← Int.cast_sum, ← Int.cast_zero]
  norm_cast

lemma chi_sq (a : ZMod p) (ha : a ≠ 0) : chi p a * chi p a = 1 := by
  have := quadraticChar_sq_one (F := ZMod p) ha
  simp only [chi, ← Int.cast_mul]
  rw [show (quadraticChar (ZMod p) a : ℤ) * (quadraticChar (ZMod p) a) = (quadraticChar (ZMod p) a)^2 by ring, this]
  norm_num


variable {p : ℕ} [Fact (Nat.Prime p)]

lemma chi_neg_one (hp4 : p % 4 = 1) : chi p (-1) = 1 := by
  have hne : (-1 : ZMod p) ≠ 0 := by
    have : (1 : ZMod p) ≠ 0 := one_ne_zero
    simpa using this
  have hsq : IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have := (quadraticChar_one_iff_isSquare (F := ZMod p) hne).mpr hsq
  simp [chi, this]

/-- the basic Jacobi sum `∑ s, χ(s)χ(s-1) = -1`. -/
lemma jac (hp4 : p % 4 = 1) : ∑ s : ZMod p, chi p s * chi p (s - 1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2
  have hq := quadraticChar_isQuadratic (F := ZMod p)
  have hne1 : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one hF
  have hJ : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = - quadraticChar (ZMod p) (-1) := by
    have := jacobiSum_nontrivial_inv (F := ZMod p) (R := ℤ) hne1
    rwa [hq.inv] at this
  have hc : quadraticChar (ZMod p) (-1) = 1 := by
    have hne : (-1 : ZMod p) ≠ 0 := by simpa using (one_ne_zero : (1:ZMod p) ≠ 0)
    exact (quadraticChar_one_iff_isSquare (F := ZMod p) hne).mpr
      (by rw [ZMod.exists_sq_eq_neg_one_iff]; omega)
  have hstep : ∀ s : ZMod p, chi p s * chi p (s - 1) = chi p s * chi p (1 - s) := by
    intro s
    have : (s - 1 : ZMod p) = (-1) * (1 - s) := by ring
    rw [this, chi_mul, chi_neg_one hp4, one_mul]
  simp only [hstep]
  have : ∑ s : ZMod p, chi p s * chi p (1 - s)
      = ((jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) : ℤ) : ℝ) := by
    simp [jacobiSum, chi, Int.cast_sum]
  rw [this, hJ, hc]
  norm_num


open Matrix



variable {p : ℕ} [Fact (Nat.Prime p)]

lemma chi_isSq {z : ZMod p} (hz : Commons.IsNonzeroSq z) : chi p z = 1 := by
  have := (quadraticChar_one_iff_isSquare (F := ZMod p) hz.1).mpr
    (by obtain ⟨r, hr⟩ := hz.2; exact ⟨r, hr⟩)
  simp [chi, this]

lemma sum_ite_card (b : ZMod p) :
    ∑ a : ZMod p, (if a = b then (0:ℝ) else 1) = (p : ℝ) - 1 := by
  have : ∑ a : ZMod p, (if a = b then (0:ℝ) else 1)
      = (∑ _a : ZMod p, (1:ℝ)) - ∑ a : ZMod p, (if a = b then (1:ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by by_cases h : a = b <;> simp [h])
  rw [this]
  simp [Finset.sum_ite_eq', ZMod.card]

lemma key (hp4 : p % 4 = 1) (b c : ZMod p) :
    ∑ a : ZMod p, chi p (a - b) * chi p (a - c) = if b = c then ((p:ℝ) - 1) else -1 := by
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl]
    have h1 : ∀ a : ZMod p, chi p (a - b) * chi p (a - b) = if a = b then (0:ℝ) else 1 := by
      intro a
      by_cases h : a = b
      · simp [h, chi_zero]
      · rw [if_neg h]; exact chi_sq _ (sub_ne_zero.mpr h)
    rw [Finset.sum_congr rfl (fun a _ => h1 a), sum_ite_card]
  · rw [if_neg hbc]
    set d : ZMod p := c - b with hd
    have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
    have := jac (p := p) hp4
    rw [← this]
    refine (Fintype.sum_equiv ((Equiv.mulLeft₀ d hd0).trans (Equiv.addLeft b))
      (fun s => chi p s * chi p (s - 1)) (fun a => chi p (a - b) * chi p (a - c)) ?_).symm
    intro s
    have e1 : b + d * s - b = d * s := by ring
    have e2 : b + d * s - c = d * (s - 1) := by rw [hd]; ring
    show chi p s * chi p (s - 1) = chi p (b + d * s - b) * chi p (b + d * s - c)
    rw [e1, e2, chi_mul, chi_mul]
    have hdd : chi p d * chi p d = 1 := chi_sq _ hd0
    rw [show chi p d * chi p s * (chi p d * chi p (s - 1))
        = (chi p d * chi p d) * (chi p s * chi p (s - 1)) from by ring, hdd, one_mul]


open Matrix
variable {p : ℕ} [Fact (Nat.Prime p)]


lemma chi_notSq {z : ZMod p} (hz : z ≠ 0) (h : ¬ Commons.IsNonzeroSq z) : chi p z = -1 := by
  have hns : ¬ IsSquare z := fun hs => h ⟨hz, hs⟩
  have hq := (quadraticChar_neg_one_iff_not_isSquare (F := ZMod p) (a := z)).mpr hns
  simp [chi, hq]

lemma card_eq (hp4 : p % 4 = 1) :
    haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
    2 * (Fintype.card (Commons.PaleyLocV p) : ℝ) + 1 = (p:ℝ) := by
  haveI : NeZero p := NeZero.of_pos (Fact.out : Nat.Prime p).pos
  have hp2 : p ≠ 2 := by omega
  have h0 : ∑ a : ZMod p, chi p a = 0 := chi_sum_zero hp2
  have hpt : ∀ a : ZMod p, chi p a + 1
      = (if Commons.IsNonzeroSq a then (2:ℝ) else 0) + (if a = 0 then (1:ℝ) else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      have hn : ¬ Commons.IsNonzeroSq (0 : ZMod p) := fun h => h.1 rfl
      rw [chi_zero, if_neg hn, if_pos rfl]
    · by_cases hs : Commons.IsNonzeroSq a
      · rw [chi_isSq hs, if_pos hs, if_neg ha]; ring
      · rw [chi_notSq ha hs, if_neg hs, if_neg ha]; ring
  have hsum : ∑ a : ZMod p, (chi p a + 1) = (p:ℝ) := by
    rw [Finset.sum_add_distrib, h0]
    simp [ZMod.card]
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib] at hsum
  have h1 : ∑ a : ZMod p, (if Commons.IsNonzeroSq a then (2:ℝ) else 0)
      = 2 * (Fintype.card (Commons.PaleyLocV p) : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [Fintype.card_subtype]
    ring
  have h2 : ∑ a : ZMod p, (if a = 0 then (1:ℝ) else 0) = 1 := by
    simp
  rw [h1, h2] at hsum
  exact hsum


open Matrix Commons
variable {p : ℕ} [Fact (Nat.Prime p)]



/-- `∑_{a,b} 1_Q(a) 1_Q(b) χ(a-b) = -(p-1)/2`, the key character-sum evaluation. -/
lemma sigma_eval (hp4 : p % 4 = 1) :
    ∑ a : ZMod p, ∑ b : ZMod p,
      ((chi p a * chi p a + chi p a) / 2) * ((chi p b * chi p b + chi p b) / 2) * chi p (a - b)
      = -((p:ℝ) - 1) / 2 := by
  have hp2 : p ≠ 2 := by omega
  have hchisum : ∑ a : ZMod p, chi p a = 0 := chi_sum_zero hp2
  have hrow : ∀ b : ZMod p, ∑ a : ZMod p, chi p (a - b) = 0 := by
    intro b
    rw [← hchisum]
    exact Fintype.sum_equiv (Equiv.subRight b) _ _ (fun a => rfl)
  have hcol : ∀ a : ZMod p, ∑ b : ZMod p, chi p (a - b) = 0 := by
    intro a
    rw [← hchisum]
    refine Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun b => ?_)
    rfl
  have hsq : ∑ a : ZMod p, chi p a * chi p a = (p:ℝ) - 1 := by
    have h1 : ∀ a : ZMod p, chi p a * chi p a = if a = 0 then (0:ℝ) else 1 := by
      intro a
      by_cases h : a = 0
      · simp [h, chi_zero]
      · rw [if_neg h]; exact chi_sq _ h
    rw [Finset.sum_congr rfl fun a _ => h1 a, sum_ite_card]
  have hqb : ∀ b : ZMod p, chi p b * chi p b = 1 - (if b = 0 then (1:ℝ) else 0) := by
    intro b
    by_cases h : b = 0
    · simp [h, chi_zero]
    · rw [if_neg h, chi_sq _ h]; ring
  have hcolq : ∀ a : ZMod p, ∑ b : ZMod p, (chi p b * chi p b) * chi p (a - b) = - chi p a := by
    intro a
    have : ∀ b : ZMod p, (chi p b * chi p b) * chi p (a - b)
        = chi p (a - b) - (if b = 0 then (1:ℝ) else 0) * chi p (a - b) := by
      intro b; rw [hqb b]; ring
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, hcol a]
    have h2 : ∑ b : ZMod p, (if b = 0 then (1:ℝ) else 0) * chi p (a - b) = chi p a := by
      rw [Finset.sum_congr rfl fun b _ => (by by_cases h : b = 0 <;> simp [h] :
        (if b = 0 then (1:ℝ) else 0) * chi p (a - b)
          = (if b = 0 then chi p a else 0))]
      simp
    rw [h2]; ring
  have hjac1 : ∑ s : ZMod p, chi p s * chi p (1 - s) = -1 := by
    have h := jac (p := p) hp4
    rw [← h]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : (s - 1 : ZMod p) = (-1) * (1 - s) := by ring
    rw [this, chi_mul, chi_neg_one hp4, one_mul]
  have hjac2 : ∀ a : ZMod p, a ≠ 0 → ∑ b : ZMod p, chi p b * chi p (a - b) = -1 := by
    intro a ha
    rw [← hjac1]
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ a ha)
      (fun s => chi p s * chi p (1 - s)) (fun b => chi p b * chi p (a - b)) ?_).symm
    intro s
    show chi p s * chi p (1 - s) = chi p (a * s) * chi p (a - a * s)
    have e : (a - a * s : ZMod p) = a * (1 - s) := by ring
    rw [e, chi_mul, chi_mul]
    have hd : chi p a * chi p a = 1 := chi_sq _ ha
    rw [show chi p a * chi p s * (chi p a * chi p (1 - s))
        = (chi p a * chi p a) * (chi p s * chi p (1 - s)) from by ring, hd, one_mul]
  -- expand
  have hexp : ∀ a b : ZMod p,
      ((chi p a * chi p a + chi p a) / 2) * ((chi p b * chi p b + chi p b) / 2) * chi p (a - b)
      = ((chi p a * chi p a) * ((chi p b * chi p b) * chi p (a - b))
        + (chi p a * chi p a) * (chi p b * chi p (a - b))
        + chi p a * ((chi p b * chi p b) * chi p (a - b))
        + chi p a * (chi p b * chi p (a - b))) / 4 := by
    intro a b; ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hexp a b]
  have hrowsum : ∀ a : ZMod p,
      (∑ b : ZMod p, ((chi p a * chi p a) * ((chi p b * chi p b) * chi p (a - b))
        + (chi p a * chi p a) * (chi p b * chi p (a - b))
        + chi p a * ((chi p b * chi p b) * chi p (a - b))
        + chi p a * (chi p b * chi p (a - b))) / 4)
      = (-2 * chi p a - 2 * (chi p a * chi p a)) / 4 := by
    intro a
    rw [← Finset.sum_div]
    congr 1
    have e1 : ∑ b : ZMod p, ((chi p a * chi p a) * ((chi p b * chi p b) * chi p (a - b))
        + (chi p a * chi p a) * (chi p b * chi p (a - b))
        + chi p a * ((chi p b * chi p b) * chi p (a - b))
        + chi p a * (chi p b * chi p (a - b)))
      = (chi p a * chi p a) * (∑ b : ZMod p, (chi p b * chi p b) * chi p (a - b))
        + (chi p a * chi p a) * (∑ b : ZMod p, chi p b * chi p (a - b))
        + chi p a * (∑ b : ZMod p, (chi p b * chi p b) * chi p (a - b))
        + chi p a * (∑ b : ZMod p, chi p b * chi p (a - b)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [e1, hcolq a]
    by_cases ha : a = 0
    · subst ha
      simp [chi_zero]
    · rw [hjac2 a ha]
      have hd : chi p a * chi p a = 1 := chi_sq _ ha
      linear_combination (-(chi p a)) * hd
  rw [Finset.sum_congr rfl fun a _ => hrowsum a, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hchisum, hsq]
  ring

lemma ind_eq (x : ZMod p) [NeZero p] :
    (chi p x * chi p x + chi p x) / 2 = if Commons.IsNonzeroSq x then (1:ℝ) else 0 := by
  by_cases hx : x = 0
  · have hn : ¬ Commons.IsNonzeroSq (0 : ZMod p) := fun h => h.1 rfl
    subst hx; rw [chi_zero, if_neg hn]; ring
  · by_cases hs : Commons.IsNonzeroSq x
    · rw [chi_isSq hs, if_pos hs]; ring
    · rw [chi_notSq hx hs, if_neg hs]; ring

theorem proof :
    ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
      haveI : NeZero p := NeZero.of_pos hp.pos
      2 * (Fintype.card (Commons.PaleyLocV p) : ℝ) = (p : ℝ) - 1 ∧
        8 * (Fintype.card {q : Commons.PaleyLocV p × Commons.PaleyLocV p //
            Commons.paleyLocAdj p q.1 q.2} : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) - 5) := by
  intro p hp hp4
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := NeZero.of_pos hp.pos
  set N : ℕ := Fintype.card (Commons.PaleyLocV p) with hN
  have hcard : 2 * (N:ℝ) + 1 = (p:ℝ) := card_eq (p := p) hp4
  refine ⟨by linarith, ?_⟩
  classical
  -- transfer the character sum to the localization
  have hsubtype : ∀ F : ZMod p → ℝ,
      ∑ a : ZMod p, (if Commons.IsNonzeroSq a then (1:ℝ) else 0) * F a
        = ∑ u : Commons.PaleyLocV p, F (u : ZMod p) := by
    intro F
    have h1 : ∀ a : ZMod p, (if Commons.IsNonzeroSq a then (1:ℝ) else 0) * F a
        = if Commons.IsNonzeroSq a then F a else 0 := by
      intro a; by_cases h : Commons.IsNonzeroSq a <;> simp [h]
    rw [Finset.sum_congr rfl fun a _ => h1 a, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) F
  have hsig := sigma_eval (p := p) hp4
  have hstep : ∀ a b : ZMod p,
      ((chi p a * chi p a + chi p a) / 2) * ((chi p b * chi p b + chi p b) / 2) * chi p (a - b)
      = (if Commons.IsNonzeroSq a then (1:ℝ) else 0) *
          ((if Commons.IsNonzeroSq b then (1:ℝ) else 0) * chi p (a - b)) := by
    intro a b; rw [ind_eq, ind_eq]; ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b] at hsig
  have hinner : ∀ a : ZMod p,
      ∑ b : ZMod p, (if Commons.IsNonzeroSq b then (1:ℝ) else 0) * chi p (a - b)
        = ∑ v : Commons.PaleyLocV p, chi p (a - (v : ZMod p)) := fun a => hsubtype _
  rw [Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum, hinner a]] at hsig
  rw [hsubtype (fun a => ∑ v : Commons.PaleyLocV p, chi p (a - (v : ZMod p)))] at hsig
  -- hsig : ∑ u, ∑ v, chi p (u - v) = -(p-1)/2
  -- edge count
  have hEcard : (Fintype.card {q : Commons.PaleyLocV p × Commons.PaleyLocV p //
      Commons.paleyLocAdj p q.1 q.2} : ℝ)
      = ∑ u : Commons.PaleyLocV p, ∑ v : Commons.PaleyLocV p,
          (if Commons.paleyLocAdj p u v then (1:ℝ) else 0) := by
    rw [Fintype.card_subtype]
    rw [Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
  have hEpt : ∀ u v : Commons.PaleyLocV p,
      (if Commons.paleyLocAdj p u v then (1:ℝ) else 0)
        = (1 + chi p ((u : ZMod p) - v)) / 2 - (if u = v then (1:ℝ)/2 else 0) := by
    intro u v
    by_cases h : u = v
    · subst h
      have hz : chi p ((u : ZMod p) - (u : ZMod p)) = 0 := by rw [sub_self]; exact chi_zero
      have hn : ¬ Commons.paleyLocAdj p u u := by
        intro hc; exact hc.1 (by simp)
      rw [if_neg hn, hz, if_pos rfl]; ring
    · have hne : ((u : ZMod p) - v) ≠ 0 := fun hc => h (Subtype.ext (sub_eq_zero.mp hc))
      by_cases hadj : Commons.paleyLocAdj p u v
      · rw [if_pos hadj, chi_isSq hadj, if_neg h]; ring
      · rw [if_neg hadj, chi_notSq hne hadj, if_neg h]; ring
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hEpt u v] at hEcard
  have hrow2 : ∀ u : Commons.PaleyLocV p,
      ∑ v : Commons.PaleyLocV p, ((1 + chi p ((u : ZMod p) - v)) / 2
        - (if u = v then (1:ℝ)/2 else 0))
      = ((N:ℝ) + ∑ v : Commons.PaleyLocV p, chi p ((u : ZMod p) - v)) / 2 - 1/2 := by
    intro u
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← hN,
        nsmul_eq_mul, mul_one]
    · simp
  rw [Finset.sum_congr rfl fun u _ => hrow2 u, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul] at hEcard
  rw [hsig] at hEcard
  rw [Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul] at hEcard
  have hp' : (p:ℝ) = 2 * (N:ℝ) + 1 := hcard.symm
  rw [hp'] at hEcard
  rw [hp', hEcard]
  ring

end Submissions.PaleyLocRegular.CharacterCount
