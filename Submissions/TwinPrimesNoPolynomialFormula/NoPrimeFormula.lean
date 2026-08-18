import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
No nonconstant integer polynomial takes prime values at all large arguments.

Given `f` with `1 ≤ f.natDegree`:

* `f * (f - C 1) * (f - C (-1))` is nonzero, hence has finitely many roots; pick `a` beyond
  all of them, so `d := f.eval a` satisfies `2 ≤ |d|`.  Put `D := |d|`.
* `f * (f - C d) * (f - C (-d))` is nonzero too; pick `k ≥ 1` so large that `n := a + k*D`
  exceeds `N` and every root of it.  Then `v := f.eval n` is none of `0, d, -d`.
* `Polynomial.sub_dvd_eval_sub` gives `(n - a) ∣ v - d`, and `n - a = k*D`, so `D ∣ v - d`;
  with `D ∣ d` this gives `D ∣ v`.
* `v ≠ 0` and `D ∣ v` give `D ≤ |v|`; `v ≠ d` and `v ≠ -d` give `|v| ≠ D`; so `2 ≤ D < |v|`
  and `v` has a divisor strictly between `1` and `|v|`, hence is not prime.
-/

namespace Submissions.TwinPrimesNoPolynomialFormula.NoPrimeFormula

open Polynomial

/-- An integer bound past every root of an integer polynomial. -/
private noncomputable def rootBd (p : ℤ[X]) : ℤ := ((p.roots.toFinset.sup fun x => x.toNat : ℕ) : ℤ)

private theorem le_rootBd {p : ℤ[X]} (hp : p ≠ 0) {x : ℤ} (hx : p.IsRoot x) :
    x ≤ rootBd p := by
  have hmem : x ∈ p.roots.toFinset := by
    simp only [Multiset.mem_toFinset]
    exact (mem_roots hp).mpr hx
  have h1 : (fun y : ℤ => y.toNat) x ≤ p.roots.toFinset.sup (fun y : ℤ => y.toNat) :=
    Finset.le_sup hmem
  have h3 : ((x.toNat : ℕ) : ℤ) ≤ rootBd p := by
    unfold rootBd
    exact_mod_cast h1
  have h2 : x ≤ ((x.toNat : ℕ) : ℤ) := Int.self_le_toNat x
  linarith

private theorem triple_ne_zero {f : ℤ[X]} (hf : 1 ≤ f.natDegree) (c : ℤ) :
    f * (f - C c) * (f - C (-c)) ≠ 0 := by
  have h0 : f ≠ 0 := by
    intro h; rw [h] at hf; simp at hf
  have h1 : f - C c ≠ 0 := by
    intro h
    have hEq : (f - C c).natDegree = f.natDegree := natDegree_sub_C
    rw [h] at hEq; simp at hEq; omega
  have h2 : f - C (-c) ≠ 0 := by
    intro h
    have hEq : (f - C (-c)).natDegree = f.natDegree := natDegree_sub_C
    rw [h] at hEq; simp at hEq; omega
  exact mul_ne_zero (mul_ne_zero h0 h1) h2

private theorem not_root_of_gt {f : ℤ[X]} (hf : 1 ≤ f.natDegree) (c x : ℤ)
    (hx : rootBd (f * (f - C c) * (f - C (-c))) < x) :
    f.eval x ≠ 0 ∧ f.eval x ≠ c ∧ f.eval x ≠ -c := by
  have hpne : f * (f - C c) * (f - C (-c)) ≠ 0 := triple_ne_zero hf c
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro hcon
    have hroot : (f * (f - C c) * (f - C (-c))).IsRoot x := by
      simp only [IsRoot, eval_mul, eval_sub, eval_C, hcon]
      ring
    have := le_rootBd hpne hroot
    omega

private theorem noPrimeFormula :
    ∀ f : Polynomial ℤ, 1 ≤ f.natDegree → ∀ N : ℤ, ∃ n : ℤ, N < n ∧ ¬ Prime (f.eval n) := by
  intro f hf N
  set a : ℤ := max N (rootBd (f * (f - C 1) * (f - C (-1)))) + 1 with hadef
  obtain ⟨ha0, ha1, ha1'⟩ := not_root_of_gt hf 1 a (by
    have := le_max_right N (rootBd (f * (f - C 1) * (f - C (-1)))); omega)
  set d : ℤ := f.eval a with hd
  have hD2 : 2 ≤ |d| := by
    rcases abs_cases d with ⟨he, hge⟩ | ⟨he, hlt⟩ <;> rw [he] <;> omega
  set D : ℤ := |d| with hDdef
  have hDpos : 0 < D := by omega
  have hDd : D ∣ d := (abs_dvd d d).mpr dvd_rfl
  set T : ℤ := max (max N a) (rootBd (f * (f - C d) * (f - C (-d)))) with hTdef
  set k : ℤ := T - a + 1 with hkdef
  have hk1 : 1 ≤ k := by
    have : a ≤ T := le_trans (le_max_right N a) (le_max_left _ _)
    omega
  set n : ℤ := a + k * D with hndef
  have hkD : k ≤ k * D := le_mul_of_one_le_right (by omega) (by omega)
  have hnT : T < n := by omega
  have hnN : N < n := by
    have : N ≤ T := le_trans (le_max_left N a) (le_max_left _ _)
    omega
  obtain ⟨hv0, hvd, hvd'⟩ := not_root_of_gt hf d n (by
    have := le_max_right (max N a) (rootBd (f * (f - C d) * (f - C (-d)))); omega)
  set v : ℤ := f.eval n with hvdef
  have hdvd : D ∣ v := by
    have hs : (n - a) ∣ (f.eval n - f.eval a) := Polynomial.sub_dvd_eval_sub n a f
    have hna : n - a = k * D := by omega
    rw [hna] at hs
    have hDs : D ∣ (v - d) := dvd_trans (dvd_mul_left D k) hs
    have := dvd_add hDs hDd
    simpa using this
  have hDle : D ≤ |v| := by
    have : D ∣ |v| := (dvd_abs D v).mpr hdvd
    exact Int.le_of_dvd (by rcases abs_cases v with ⟨he, _⟩ | ⟨he, _⟩ <;> omega) this
  have hDne : D ≠ |v| := by
    intro hcon
    rcases abs_cases v with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rcases abs_cases d with ⟨he2, _⟩ | ⟨he2, _⟩ <;> omega
  have hDlt : D < |v| := by omega
  refine ⟨n, hnN, ?_⟩
  intro hprime
  have hnat : Nat.Prime v.natAbs := Int.prime_iff_natAbs_prime.mp hprime
  have hdvdnat : D.natAbs ∣ v.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
  have hvnat : (v.natAbs : ℤ) = |v| := (Int.abs_eq_natAbs v).symm
  have hDnat : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg (le_of_lt hDpos)
  have hDlt2 : (D.natAbs : ℤ) < (v.natAbs : ℤ) := by rw [hDnat, hvnat]; exact hDlt
  have hDge2 : 2 ≤ (D.natAbs : ℤ) := by rw [hDnat]; exact hD2
  have hlt : D.natAbs < v.natAbs := by exact_mod_cast hDlt2
  have hge : 2 ≤ D.natAbs := by exact_mod_cast hDge2
  rcases hnat.eq_one_or_self_of_dvd _ hdvdnat with hcase | hcase <;> omega

/-- The elimination: no nonconstant integer polynomial is prime-valued at all large
arguments, and in particular none produces twin prime pairs at all large arguments. -/
theorem proof :
  (∀ f : Polynomial ℤ, 1 ≤ f.natDegree → ∀ N : ℤ, ∃ n : ℤ, N < n ∧ ¬ Prime (f.eval n))
  ∧ (∀ f : Polynomial ℤ, 1 ≤ f.natDegree → ∀ N : ℤ, ∃ n : ℤ, N < n ∧
        ¬ (Prime (f.eval n) ∧ Prime (f.eval n + 2))) := by
  refine ⟨noPrimeFormula, ?_⟩
  intro f hf N
  obtain ⟨n, hn, hnp⟩ := noPrimeFormula f hf N
  exact ⟨n, hn, fun h => hnp h.1⟩

end Submissions.TwinPrimesNoPolynomialFormula.NoPrimeFormula
