import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Group.Even
import Commons.SetPairSystem

/-!
# BlockProductOptimum, proved

Method.  Write `P = ∏ (uᵢvᵢ+1)`, `p = ∑ uᵢ`, `q = ∑ vᵢ`, and `D t = 5 - t % 2` (so `D` is `5`
on evens, `4` on odds).  The whole content is the single potential inequality

  `25 * P ^ 4 ≤ 5 ^ (p+q) * D p * D q`,

which is multiplicative over blocks and therefore proves itself by one list induction.  The
per-block step is Cauchy–Schwarz `(uv+1)^2 ≤ (u²+1)(v²+1)` followed by the one-variable
engine `(u²+1)^2 * D a ≤ 5^u * D (u+a)`, whose two cases are `(u²+1)^2 ≤ 5^u` (tight at
`u = 0, 2`) and `5(u²+1)^2 ≤ 4·5^u` for odd `u` (tight at `u = 1, 3`).  Reading the potential
at `p = q = n` gives the even branch on the nose; the odd branch needs the `D` factors, which
are both `4` exactly when `p = q = n` is odd, and that is where the `2·5^((n-1)/2)` spelling
comes from.
-/

namespace Submissions.BlockProductOptimum.PotentialProof

/-- `D t = 5 - t % 2`: the parity discount, `5` on evens and `4` on odds. -/
def D (t : ℕ) : ℕ := 5 - t % 2

lemma D_even {t : ℕ} (h : t % 2 = 0) : D t = 5 := by simp [D, h]
lemma D_odd  {t : ℕ} (h : t % 2 = 1) : D t = 4 := by simp [D, h]
lemma D_le (t : ℕ) : D t ≤ 5 := by simp only [D]; omega

/-- Two-term Cauchy–Schwarz. -/
lemma cs (u v : ℕ) : (u*v+1)^2 ≤ (u^2+1)*(v^2+1) := by
  have h : (2*u*v : ℤ) ≤ (u:ℤ)^2 + (v:ℤ)^2 := by nlinarith [sq_nonneg ((u:ℤ) - v)]
  have h' : 2*u*v ≤ u^2+v^2 := by exact_mod_cast h
  nlinarith [h']

/-- `(u^2+1)^2 ≤ 5^u`, tight at `u = 0` and `u = 2`. -/
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
      have step : ((k+3)^2+1)^2 ≤ 5 * ((k+2)^2+1)^2 := by
        rw [hid]; exact Nat.le_add_right _ _
      calc ((k+3)^2+1)^2 ≤ 5 * ((k+2)^2+1)^2 := step
        _ ≤ 5 * 5^(k+2) := Nat.mul_le_mul_left 5 h
        _ = 5^(k+3) := by ring

/-- `5*(u^2+1)^2 ≤ 4*5^u` for odd `u`, tight at `u = 1` and `u = 3`. -/
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

/-- The one-variable engine. -/
lemma keyK (u a : ℕ) : (u^2+1)^2 * D a ≤ 5^u * D (u+a) := by
  rcases Nat.even_or_odd u with he | ho
  · have hu : u % 2 = 0 := Nat.even_iff.mp he
    have h : (u+a) % 2 = a % 2 := by omega
    simp only [D, h]
    exact Nat.mul_le_mul_right _ (key2 u)
  · obtain ⟨j, hj⟩ := ho
    have hu : u % 2 = 1 := by omega
    have h3 : 5*(u^2+1)^2 ≤ 4*5^u := by
      have := key3 j
      have e : 2*j+1 = u := by omega
      rw [e] at this; exact this
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

def blocks (l : List (ℕ × ℕ)) : ℕ := (l.map (fun p => p.1 * p.2 + 1)).prod
def sfst (l : List (ℕ × ℕ)) : ℕ := (l.map Prod.fst).sum
def ssnd (l : List (ℕ × ℕ)) : ℕ := (l.map Prod.snd).sum

/-- The potential bound: multiplicative over blocks, hence one induction. -/
theorem potential (l : List (ℕ × ℕ)) :
    25 * (blocks l)^4 ≤ 5^(sfst l + ssnd l) * D (sfst l) * D (ssnd l) := by
  induction l with
  | nil => simp [blocks, sfst, ssnd, D]
  | cons p t ih =>
    obtain ⟨u, v⟩ := p
    have hb : blocks ((u,v) :: t) = (u*v+1) * blocks t := by simp [blocks]
    have hp : sfst ((u,v) :: t) = u + sfst t := by simp [sfst]
    have hq : ssnd ((u,v) :: t) = v + ssnd t := by simp [ssnd]
    rw [hb, hp, hq]
    have h1 : (u*v+1)^4 ≤ (u^2+1)^2 * (v^2+1)^2 := by
      have hcs := cs u v
      calc (u*v+1)^4 = ((u*v+1)^2)^2 := by ring
        _ ≤ ((u^2+1)*(v^2+1))^2 := Nat.pow_le_pow_left hcs 2
        _ = (u^2+1)^2 * (v^2+1)^2 := by ring
    calc 25 * ((u*v+1) * blocks t)^4
        = (u*v+1)^4 * (25 * (blocks t)^4) := by ring
      _ ≤ ((u^2+1)^2 * (v^2+1)^2) * (5^(sfst t + ssnd t) * D (sfst t) * D (ssnd t)) :=
          Nat.mul_le_mul h1 ih
      _ = 5^(sfst t + ssnd t) * ((u^2+1)^2 * D (sfst t)) * ((v^2+1)^2 * D (ssnd t)) := by ring
      _ ≤ 5^(sfst t + ssnd t) * (5^u * D (u + sfst t)) * (5^v * D (v + ssnd t)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (keyK u (sfst t))) (keyK v (ssnd t))
      _ = 5^(u + sfst t + (v + ssnd t)) * D (u + sfst t) * D (v + ssnd t) := by ring

/-- Fourth roots in `ℕ`. -/
lemma pow4_le (a b : ℕ) (h : a^4 ≤ b^4) : a ≤ b := by
  by_contra hc
  have hc' : b < a := Nat.lt_of_not_le hc
  exact absurd h (not_le.mpr (Nat.pow_lt_pow_left hc' (by norm_num)))

theorem proof :
    ∀ (n : ℕ) (l : List (ℕ × ℕ)),
      (l.map Prod.fst).sum ≤ n → (l.map Prod.snd).sum ≤ n →
        (Even n → (l.map (fun p => p.1 * p.2 + 1)).prod ≤ 5 ^ (n / 2)) ∧
        (Odd n → (l.map (fun p => p.1 * p.2 + 1)).prod ≤ 2 * 5 ^ ((n - 1) / 2)) := by
  intro n l hp hq
  have hP := potential l
  set p := sfst l with hpdef
  set q := ssnd l with hqdef
  have hp' : p ≤ n := hp
  have hq' : q ≤ n := hq
  set P := blocks l with hPdef
  constructor
  · rintro ⟨k, hk⟩
    have hn : n = 2*k := by omega
    have h1 : 25 * P^4 ≤ 5^(p+q) * 25 := by
      calc 25 * P^4 ≤ 5^(p+q) * D p * D q := hP
        _ ≤ 5^(p+q) * 5 * 5 := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (D_le p)) (D_le q)
        _ = 5^(p+q) * 25 := by ring
    have h2 : P^4 ≤ 5^(p+q) := by omega
    have h3 : P^4 ≤ 5^(4*k) := le_trans h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : (5^k)^4 = 5^(4*k) := by rw [← pow_mul]; ring_nf
    have : P ≤ 5^k := pow4_le _ _ (by rw [h4]; exact h3)
    have hnk : n/2 = k := by omega
    rw [hnk]; exact this
  · rintro ⟨k, hk⟩
    have hn : n = 2*k+1 := by omega
    have hgoal : P^4 ≤ 16 * 5^(4*k) := by
      by_cases hcase : p + q ≤ 4*k+1
      · have h1 : 25 * P^4 ≤ 5^(p+q) * 25 := by
          calc 25 * P^4 ≤ 5^(p+q) * D p * D q := hP
            _ ≤ 5^(p+q) * 5 * 5 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (D_le p)) (D_le q)
            _ = 5^(p+q) * 25 := by ring
        have h2 : P^4 ≤ 5^(p+q) := by omega
        have h3 : P^4 ≤ 5^(4*k+1) := le_trans h2 (Nat.pow_le_pow_right (by norm_num) hcase)
        have h5 : 5^(4*k+1) = 5 * 5^(4*k) := by ring
        calc P^4 ≤ 5^(4*k+1) := h3
          _ = 5 * 5^(4*k) := h5
          _ ≤ 16 * 5^(4*k) := Nat.mul_le_mul_right _ (by norm_num)
      · have hpq : p = n ∧ q = n := by omega
        obtain ⟨hpn, hqn⟩ := hpq
        have hodd : n % 2 = 1 := by omega
        have hDp : D p = 4 := by rw [hpn]; exact D_odd hodd
        have hDq : D q = 4 := by rw [hqn]; exact D_odd hodd
        have h1 : 25 * P^4 ≤ 5^(p+q) * 4 * 4 := by rw [hDp, hDq] at hP; exact hP
        have hpq2 : p + q = 4*k+2 := by omega
        have h2 : 5^(p+q) * 4 * 4 = 25 * (16 * 5^(4*k)) := by
          rw [hpq2]; ring
        omega
    have h4 : (2*5^k)^4 = 16 * 5^(4*k) := by
      have : (5^k)^4 = 5^(4*k) := by rw [← pow_mul]; ring_nf
      calc (2*5^k)^4 = 16 * (5^k)^4 := by ring
        _ = 16 * 5^(4*k) := by rw [this]
    have : P ≤ 2*5^k := pow4_le _ _ (by rw [h4]; exact hgoal)
    have hnk : (n-1)/2 = k := by omega
    rw [hnk]; exact this

end Submissions.BlockProductOptimum.PotentialProof
