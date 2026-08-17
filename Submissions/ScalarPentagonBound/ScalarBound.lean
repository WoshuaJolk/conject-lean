import Mathlib

/-!
Recovered from report 107's `Scalar.lean` (the campaign's P4), inlined and renamespaced.
Route: AM-GM `4uv ≤ (u+v)²`; the one-variable bound `(s²+4)^4 ≤ 256·5^s` for `s ≥ 4` by
induction from the rational step `20(s²+2s+5) ≤ 29(s²+4)` (i.e. `(s−4)(9s−4) ≥ 0`) together
with `29^4 = 707281 < 800000 = 5·20^4`; the strict version for `s ≥ 5` pins the equality case
to `(2,2)`; small `s` by `interval_cases`/`norm_num`.
-/

namespace Submissions.ScalarPentagonBound.ScalarBound

/-
Hunt3 / CosetCover / Scalar.lean — P4's scalar inequality, run 3 wave 2
(leaf 107, secondary). Source: 05 App II (STATE.md §1 P4).

`(uv + 1)^4 ≤ 5^(u+v)` for naturals `u, v ≥ 1`, with equality iff `u = v = 2`.

Route: AM-GM gives `4(uv+1) ≤ s² + 4` with `s = u + v`; the one-variable bound
`(s²+4)^4 ≤ 256·5^s` for `s ≥ 4` follows by induction from the rational step
`20(s²+2s+5) ≤ 29(s²+4)` (i.e. `(s-4)(9s-4) ≥ 0`) and `29^4 < 5·20^4`; small
`s` by direct evaluation. The strict version for `s ≥ 5` pins equality to
`(2,2)`.
-/

namespace CosetCover

/-- Induction step: `((s+1)²+4)^4 ≤ 5·(s²+4)^4` for `s ≥ 4`. -/
theorem scalar_step {s : ℕ} (hs : 4 ≤ s) : ((s + 1) ^ 2 + 4) ^ 4 ≤ 5 * (s ^ 2 + 4) ^ 4 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 4 := ⟨s - 4, by omega⟩
  have h1 : 20 * ((t + 4 + 1) ^ 2 + 4) ≤ 29 * ((t + 4) ^ 2 + 4) := by nlinarith
  have h2 : (20 * ((t + 4 + 1) ^ 2 + 4)) ^ 4 ≤ (29 * ((t + 4) ^ 2 + 4)) ^ 4 :=
    Nat.pow_le_pow_left h1 4
  have h3 : 160000 * (((t + 4 + 1) ^ 2 + 4) ^ 4) ≤ 160000 * (5 * ((t + 4) ^ 2 + 4) ^ 4) := by
    calc 160000 * (((t + 4 + 1) ^ 2 + 4) ^ 4)
        = (20 * ((t + 4 + 1) ^ 2 + 4)) ^ 4 := by ring
      _ ≤ (29 * ((t + 4) ^ 2 + 4)) ^ 4 := h2
      _ = 707281 * (((t + 4) ^ 2 + 4) ^ 4) := by ring
      _ ≤ 800000 * (((t + 4) ^ 2 + 4) ^ 4) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 160000 * (5 * ((t + 4) ^ 2 + 4) ^ 4) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

/-- `(s²+4)^4 ≤ 256·5^s` for `s ≥ 4` (equality at `s = 4`). -/
theorem sq_bound {s : ℕ} (hs : 4 ≤ s) : (s ^ 2 + 4) ^ 4 ≤ 256 * 5 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    calc ((s + 1) ^ 2 + 4) ^ 4 ≤ 5 * (s ^ 2 + 4) ^ 4 := scalar_step hs
      _ ≤ 5 * (256 * 5 ^ s) := Nat.mul_le_mul_left _ ih
      _ = 256 * 5 ^ (s + 1) := by ring

/-- Strict version: `(s²+4)^4 < 256·5^s` for `s ≥ 5`. -/
theorem sq_bound_strict {s : ℕ} (hs : 5 ≤ s) : (s ^ 2 + 4) ^ 4 < 256 * 5 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    calc ((s + 1) ^ 2 + 4) ^ 4 ≤ 5 * (s ^ 2 + 4) ^ 4 := scalar_step (by omega)
      _ < 5 * (256 * 5 ^ s) := by nlinarith
      _ = 256 * 5 ^ (s + 1) := by ring

/-- AM-GM for naturals: `4uv ≤ (u+v)²`. -/
theorem four_mul_le_sq_add (u v : ℕ) : 4 * (u * v) ≤ (u + v) ^ 2 := by
  have h : (4 * ((u : ℤ) * v)) ≤ ((u : ℤ) + v) ^ 2 := by nlinarith [sq_nonneg ((u : ℤ) - v)]
  exact_mod_cast h

/-- **P4 (inequality part).** `(uv+1)^4 ≤ 5^(u+v)` for `u, v ≥ 1`. -/
theorem scalar_ineq {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (u * v + 1) ^ 4 ≤ 5 ^ (u + v) := by
  by_cases hs : 4 ≤ u + v
  · have h1 : 4 * (u * v + 1) ≤ (u + v) ^ 2 + 4 := by
      have := four_mul_le_sq_add u v
      omega
    have h3 : 256 * ((u * v + 1) ^ 4) ≤ 256 * (5 ^ (u + v)) := by
      calc 256 * ((u * v + 1) ^ 4) = (4 * (u * v + 1)) ^ 4 := by ring
        _ ≤ ((u + v) ^ 2 + 4) ^ 4 := Nat.pow_le_pow_left h1 4
        _ ≤ 256 * 5 ^ (u + v) := sq_bound hs
    exact Nat.le_of_mul_le_mul_left h3 (by norm_num)
  · have hu2 : u ≤ 2 := by omega
    have hv2 : v ≤ 2 := by omega
    interval_cases u <;> interval_cases v <;> norm_num

/-- **P4 (equality part).** For `u, v ≥ 1`: `(uv+1)^4 = 5^(u+v)` iff `u = v = 2`. -/
theorem scalar_eq_iff {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (u * v + 1) ^ 4 = 5 ^ (u + v) ↔ u = 2 ∧ v = 2 := by
  constructor
  · intro heq
    by_cases hs : u + v ≤ 4
    · have hu3 : u ≤ 3 := by omega
      have hv3 : v ≤ 3 := by omega
      interval_cases u <;> interval_cases v <;> simp_all
    · exfalso
      have hstrict := sq_bound_strict (s := u + v) (by omega)
      have h1 : 4 * (u * v + 1) ≤ (u + v) ^ 2 + 4 := by
        have := four_mul_le_sq_add u v
        omega
      have h3 : 256 * ((u * v + 1) ^ 4) < 256 * (5 ^ (u + v)) := by
        calc 256 * ((u * v + 1) ^ 4) = (4 * (u * v + 1)) ^ 4 := by ring
          _ ≤ ((u + v) ^ 2 + 4) ^ 4 := Nat.pow_le_pow_left h1 4
          _ < 256 * 5 ^ (u + v) := hstrict
      have h4 : (u * v + 1) ^ 4 < 5 ^ (u + v) := Nat.lt_of_mul_lt_mul_left h3
      exact absurd heq (Nat.ne_of_lt h4)
  · rintro ⟨rfl, rfl⟩
    norm_num

end CosetCover

/-- The canonical proposition of `Statements.ScalarPentagonBound`. -/
theorem proof :
    ∀ u v : ℕ, 1 ≤ u → 1 ≤ v →
      (u * v + 1) ^ 4 ≤ 5 ^ (u + v) ∧
      ((u * v + 1) ^ 4 = 5 ^ (u + v) ↔ u = 2 ∧ v = 2) :=
  fun _ _ hu hv => ⟨CosetCover.scalar_ineq hu hv, CosetCover.scalar_eq_iff hu hv⟩

end Submissions.ScalarPentagonBound.ScalarBound
