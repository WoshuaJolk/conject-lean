import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic
import Commons.SetPairSystem

/-!
# GroupInvariantFGKFromOrbitProduct, proved

Two parts.  `Arith` is the Finset form of `BlockProductOptimum` (#15): with both coordinate
sums at most `n`, `prod (u_i v_i + 1)` is at most the FGK value, proved through the
parity-refined potential `25 P^4 <= 5^(p+q) * D p * D q` with `D t = 5 - t % 2`.  The theorem
then instantiates the orbit-product hypothesis at the orbit quotient of `X`, and observes that
the per-orbit counts of `A 1` and of `B 1` sum to `|A 1|` and `|B 1|`, both at most `n`.
No commutativity is used anywhere.
-/

namespace Submissions.GroupInvariantFGKFromOrbitProduct.Wiring

/-! ## The arithmetic ceiling: the exact optimum of the block-product functional -/

namespace Arith
open Finset

/-- `D t = 5 - t % 2`: the parity discount, `5` on evens and `4` on odds. -/
def D (t : ℕ) : ℕ := 5 - t % 2
lemma D_even {t : ℕ} (h : t % 2 = 0) : D t = 5 := by simp [D, h]
lemma D_odd  {t : ℕ} (h : t % 2 = 1) : D t = 4 := by simp [D, h]
lemma D_le (t : ℕ) : D t ≤ 5 := by simp only [D]; omega

lemma cs (u v : ℕ) : (u*v+1)^2 ≤ (u^2+1)*(v^2+1) := by
  have h : (2*u*v : ℤ) ≤ (u:ℤ)^2 + (v:ℤ)^2 := by nlinarith [sq_nonneg ((u:ℤ) - v)]
  have h' : 2*u*v ≤ u^2+v^2 := by exact_mod_cast h
  nlinarith [h']

lemma key2 : ∀ u : ℕ, (u^2+1)^2 ≤ 5^u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    match u with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | (k+3) =>
      have h := ih (k+2) (by omega)
      have hid : 5*((k+2)^2+1)^2 = ((k+3)^2+1)^2 + (4*k^4+28*k^3+74*k^2+80*k+25) := by ring
      have step : ((k+3)^2+1)^2 ≤ 5 * ((k+2)^2+1)^2 := by rw [hid]; exact Nat.le_add_right _ _
      calc ((k+3)^2+1)^2 ≤ 5 * ((k+2)^2+1)^2 := step
        _ ≤ 5 * 5^(k+2) := Nat.mul_le_mul_left 5 h
        _ = 5^(k+3) := by ring

lemma key3 : ∀ j : ℕ, 5*((2*j+1)^2+1)^2 ≤ 4*5^(2*j+1) := by
  intro j
  induction j with
  | zero => norm_num
  | succ i ih =>
    have hid : 25*((2*i+1)^2+1)^2
        = ((2*(i+1)+1)^2+1)^2 + (384*i^4+704*i^3+576*i^2+160*i) := by ring
    have step : ((2*(i+1)+1)^2+1)^2 ≤ 25 * ((2*i+1)^2+1)^2 := by
      rw [hid]; exact Nat.le_add_right _ _
    calc 5*((2*(i+1)+1)^2+1)^2 ≤ 5 * (25 * ((2*i+1)^2+1)^2) := Nat.mul_le_mul_left 5 step
      _ = 25 * (5*((2*i+1)^2+1)^2) := by ring
      _ ≤ 25 * (4*5^(2*i+1)) := Nat.mul_le_mul_left 25 ih
      _ = 4*5^(2*(i+1)+1) := by ring

lemma keyK (u a : ℕ) : (u^2+1)^2 * D a ≤ 5^u * D (u+a) := by
  rcases Nat.even_or_odd u with he | ho
  · have hu : u % 2 = 0 := Nat.even_iff.mp he
    have h : (u+a) % 2 = a % 2 := by omega
    simp only [D, h]
    exact Nat.mul_le_mul_right _ (key2 u)
  · obtain ⟨j, hj⟩ := ho
    have hu : u % 2 = 1 := by omega
    have h3 : 5*(u^2+1)^2 ≤ 4*5^u := by
      have hk := key3 j
      have e : 2*j+1 = u := by omega
      rw [e] at hk
      exact hk
    rcases Nat.even_or_odd a with hae | hao
    · have ha : a % 2 = 0 := Nat.even_iff.mp hae
      have hua : (u+a) % 2 = 1 := by omega
      rw [D_even ha, D_odd hua]
      calc (u^2+1)^2 * 5 = 5*(u^2+1)^2 := by ring
        _ ≤ 4*5^u := h3
        _ = 5^u * 4 := by ring
    · obtain ⟨i, hi⟩ := hao
      have ha : a % 2 = 1 := by omega
      have hua : (u+a) % 2 = 0 := by omega
      rw [D_odd ha, D_even hua]
      calc (u^2+1)^2 * 4 ≤ 5^u * 4 := Nat.mul_le_mul_right _ (key2 u)
        _ ≤ 5^u * 5 := Nat.mul_le_mul_left _ (by norm_num)

variable {α : Type*} [DecidableEq α]

theorem potentialF (s : Finset α) (u v : α → ℕ) :
    25 * (∏ i ∈ s, (u i * v i + 1))^4
      ≤ 5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i)) * D (∑ i ∈ s, u i) * D (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : (u x * v x+1)^4 ≤ ((u x)^2+1)^2 * ((v x)^2+1)^2 := by
      have hcs := cs (u x) (v x)
      calc (u x * v x+1)^4 = ((u x * v x+1)^2)^2 := by ring
        _ ≤ (((u x)^2+1)*((v x)^2+1))^2 := Nat.pow_le_pow_left hcs 2
        _ = ((u x)^2+1)^2 * ((v x)^2+1)^2 := by ring
    calc 25 * ((u x * v x + 1) * ∏ i ∈ s, (u i * v i + 1))^4
        = (u x * v x+1)^4 * (25 * (∏ i ∈ s, (u i * v i + 1))^4) := by ring
      _ ≤ (((u x)^2+1)^2 * ((v x)^2+1)^2)
            * (5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i)) * D (∑ i ∈ s, u i) * D (∑ i ∈ s, v i)) :=
          Nat.mul_le_mul h1 ih
      _ = 5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i))
            * (((u x)^2+1)^2 * D (∑ i ∈ s, u i)) * (((v x)^2+1)^2 * D (∑ i ∈ s, v i)) := by ring
      _ ≤ 5^((∑ i ∈ s, u i) + (∑ i ∈ s, v i))
            * (5^(u x) * D (u x + ∑ i ∈ s, u i)) * (5^(v x) * D (v x + ∑ i ∈ s, v i)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (keyK (u x) (∑ i ∈ s, u i)))
            (keyK (v x) (∑ i ∈ s, v i))
      _ = 5^((u x + ∑ i ∈ s, u i) + (v x + ∑ i ∈ s, v i))
            * D (u x + ∑ i ∈ s, u i) * D (v x + ∑ i ∈ s, v i) := by ring

lemma pow4_le (a b : ℕ) (h : a^4 ≤ b^4) : a ≤ b := by
  by_contra hc
  exact absurd h (not_le.mpr (Nat.pow_lt_pow_left (Nat.lt_of_not_le hc) (by norm_num)))

/-- The block optimum. -/
theorem blockBound (s : Finset α) (u v : α → ℕ) (n : ℕ)
    (hu : (∑ i ∈ s, u i) ≤ n) (hv : (∑ i ∈ s, v i) ≤ n) :
    (Even n → (∏ i ∈ s, (u i * v i + 1)) ≤ 5^(n/2)) ∧
    (Odd n → (∏ i ∈ s, (u i * v i + 1)) ≤ 2 * 5^((n-1)/2)) := by
  have hP := potentialF s u v
  set p := ∑ i ∈ s, u i
  set q := ∑ i ∈ s, v i
  set P := ∏ i ∈ s, (u i * v i + 1)
  constructor
  · rintro ⟨k, hk⟩
    have h1 : 25 * P^4 ≤ 5^(p+q) * 25 := by
      calc 25 * P^4 ≤ 5^(p+q) * D p * D q := hP
        _ ≤ 5^(p+q) * 5 * 5 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (D_le p)) (D_le q)
        _ = 5^(p+q) * 25 := by ring
    have h2 : P^4 ≤ 5^(p+q) := by omega
    have h3 : P^4 ≤ 5^(4*k) := le_trans h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : (5^k)^4 = 5^(4*k) := by rw [← pow_mul]; ring_nf
    have hle : P ≤ 5^k := pow4_le _ _ (by rw [h4]; exact h3)
    have hnk : n/2 = k := by omega
    rw [hnk]; exact hle
  · rintro ⟨k, hk⟩
    have hgoal : P^4 ≤ 16 * 5^(4*k) := by
      by_cases hcase : p + q ≤ 4*k+1
      · have h1 : 25 * P^4 ≤ 5^(p+q) * 25 := by
          calc 25 * P^4 ≤ 5^(p+q) * D p * D q := hP
            _ ≤ 5^(p+q) * 5 * 5 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (D_le p)) (D_le q)
            _ = 5^(p+q) * 25 := by ring
        have h2 : P^4 ≤ 5^(p+q) := by omega
        calc P^4 ≤ 5^(4*k+1) := le_trans h2 (Nat.pow_le_pow_right (by norm_num) hcase)
          _ = 5 * 5^(4*k) := by ring
          _ ≤ 16 * 5^(4*k) := Nat.mul_le_mul_right _ (by norm_num)
      · have hpn : p = n := by omega
        have hqn : q = n := by omega
        have hodd : n % 2 = 1 := by omega
        have hDp : D p = 4 := by rw [hpn]; exact D_odd hodd
        have hDq : D q = 4 := by rw [hqn]; exact D_odd hodd
        have h1 : 25 * P^4 ≤ 5^(p+q) * 4 * 4 := by rw [hDp, hDq] at hP; exact hP
        have hpq2 : p + q = 4*k+2 := by omega
        have h2 : 5^(p+q) * 4 * 4 = 25 * (16 * 5^(4*k)) := by rw [hpq2]; ring
        omega
    have h4 : (2*5^k)^4 = 16 * 5^(4*k) := by
      have e : (5^k)^4 = 5^(4*k) := by rw [← pow_mul]; ring_nf
      calc (2*5^k)^4 = 16 * (5^k)^4 := by ring
        _ = 16 * 5^(4*k) := by rw [e]
    have hle : P ≤ 2*5^k := pow4_le _ _ (by rw [h4]; exact hgoal)
    have hnk : (n-1)/2 = k := by omega
    rw [hnk]; exact hle

end Arith


open Finset MulAction

theorem proof :
    (∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
      (A B : G → Finset X),
      (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
      (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
      (∀ g : G, A g ∩ B g = ∅) →
      (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (π : X → Ω),
        (∀ x y : X, π x = π y ↔ ∃ g : G, g • x = y) →
          Fintype.card G ≤
            ∏ ω : Ω, (((A 1).filter (fun x => π x = ω)).card
                      * ((B 1).filter (fun y => π y = ω)).card + 1)) →
    ∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
      (n : ℕ) (A B : G → Finset X),
      (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
      (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
      (∀ g : G, (A g).card ≤ n) →
      (∀ g : G, (B g).card ≤ n) →
      (∀ g : G, A g ∩ B g = ∅) →
      (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
        (Even n → Fintype.card G ≤ 5 ^ (n / 2)) ∧
        (Odd n → Fintype.card G ≤ 2 * 5 ^ ((n - 1) / 2)) := by
  intro H G X _ _ _ _ _ n A B hA hB hcA hcB hAB hcross
  classical
  -- name the orbits by the orbit quotient
  let Ω := Quotient (MulAction.orbitRel G X)
  have : Fintype Ω := Fintype.ofFinite _
  let π : X → Ω := fun x => Quotient.mk _ x
  have hπ : ∀ x y : X, π x = π y ↔ ∃ g : G, g • x = y := by
    intro x y
    constructor
    · intro h
      have h' : (MulAction.orbitRel G X).r x y := Quotient.exact h
      rw [MulAction.orbitRel_apply] at h'
      obtain ⟨g, hg⟩ := h'
      exact ⟨g⁻¹, by rw [← hg]; simp⟩
    · rintro ⟨g, rfl⟩
      refine Quotient.sound ?_
      have hx : x ∈ MulAction.orbit G (g • x) := ⟨g⁻¹, by simp⟩
      exact (MulAction.orbitRel_apply).mpr hx
  have hprod := H G X A B hA hB hAB hcross Ω π hπ
  -- the per-orbit counts sum to the total counts
  have hsumA : ∑ ω : Ω, ((A 1).filter (fun x => π x = ω)).card = (A 1).card :=
    (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (π x))).symm
  have hsumB : ∑ ω : Ω, ((B 1).filter (fun y => π y = ω)).card = (B 1).card :=
    (Finset.card_eq_sum_card_fiberwise (fun y _ => Finset.mem_univ (π y))).symm
  have hblock := Arith.blockBound (Finset.univ : Finset Ω)
      (fun ω => ((A 1).filter (fun x => π x = ω)).card)
      (fun ω => ((B 1).filter (fun y => π y = ω)).card) n
      (by rw [hsumA]; exact hcA 1) (by rw [hsumB]; exact hcB 1)
  exact ⟨fun he => le_trans hprod (hblock.1 he), fun ho => le_trans hprod (hblock.2 ho)⟩

end Submissions.GroupInvariantFGKFromOrbitProduct.Wiring
