import Mathlib

open Finset

/-!
# Proof of `Statements.BollobasCoverTensorBridge.statement`

`sum_r prod_j [r in A_j (i_j)]` over `ZMod 2` counts, mod 2, the ground-set elements lying in
every `A_j (i_j)` -- that is, it is the cardinality of the k-wise intersection reduced mod 2.
The Bollobas condition and the tensor identity are then the same statement about that number,
separated only by a case split on its parity.

The definitions are restated rather than imported, because canonical statements carry `sorry`
and submissions may not import them.
-/

namespace Submissions.BollobasCoverTensorBridge.WoshuaJolk

def kInter {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (f : Fin k → Fin N) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter (fun r => ∀ j : Fin k, r ∈ A j (f j))

def IsBollobasTuple (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)) : Prop :=
  ∀ f : Fin k → Fin N, ((kInter A f).card % 2 = 0 ↔ (image f univ).card < t)

def T (k t N : ℕ) (i : Fin k → Fin N) : ZMod 2 :=
  if t ≤ (image i univ).card then 1 else 0

abbrev statement : Prop :=
  ∀ (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)),
    IsBollobasTuple k t N m A ↔
      ∀ i : Fin k → Fin N,
        (∑ r : Fin m, ∏ j : Fin k, (if r ∈ A j (i j) then (1 : ZMod 2) else 0)) = T k t N i

theorem hsum {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (i : Fin k → Fin N) :
    (∑ r : Fin m, ∏ j : Fin k, (if r ∈ A j (i j) then (1 : ZMod 2) else 0))
      = ((kInter A i).card : ZMod 2) := by
  rw [kInter, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : ∀ j : Fin k, r ∈ A j (i j)
  · rw [if_pos hr]
    exact Finset.prod_eq_one fun j _ => if_pos (hr j)
  · rw [if_neg hr]
    push_neg at hr
    obtain ⟨j, hj⟩ := hr
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem bridge (t c x : ℕ) :
    ((c % 2 = 0 ↔ x < t) ↔ ((c : ZMod 2) = if t ≤ x then 1 else 0)) := by
  have h : (c : ZMod 2) = ((c % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod c 2).symm
  rw [h, ← not_le]
  rcases Nat.mod_two_eq_zero_or_one c with h2 | h2 <;> rw [h2] <;>
    by_cases hx : t ≤ x <;> simp [hx]

theorem proof : statement := by
  intro k t N m A
  constructor
  · intro hB i
    rw [hsum A i]
    simp only [T]
    exact (bridge t _ _).mp (hB i)
  · intro hS f
    have hthis := hS f
    rw [hsum A f] at hthis
    simp only [T] at hthis
    exact (bridge t _ _).mpr hthis

end Submissions.BollobasCoverTensorBridge.WoshuaJolk
