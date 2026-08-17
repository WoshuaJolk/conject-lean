import Mathlib

open Finset

/-!
# Proof of `Statements.OVParityInterchange.statement`

The adjoined element `Fin.last m` lies in every adjoined set, so it lies in every adjoined
intersection, and `castSucc` is injective and never hits it. Hence the intersection's
cardinality rises by exactly one, uniformly in `k`, `N`, `m`, `A` and `f` -- including
`k = 0`, where both intersections are the whole ground set. `Nat.even_add_one` then swaps
`Even ... <-> t <= card` for `Even ... <-> card < t`, which is precisely the source's
"add an auxiliary element ... to interchange the parity" clause.

The definitions are restated here rather than imported, because canonical statements carry
`sorry` and submissions may not import them.
-/

namespace Submissions.OVParityInterchange.WoshuaJolk

def kInter {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (f : Fin k → Fin N) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter (fun r => ∀ j : Fin k, r ∈ A j (f j))

def OVHyp (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)) : Prop :=
  ∀ f : Fin k → Fin N, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

def IsBollobasTuple (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)) : Prop :=
  ∀ f : Fin k → Fin N, (Even (kInter A f).card ↔ (image f univ).card < t)

def adjoin {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) :
    Fin k → Fin N → Finset (Fin (m + 1)) :=
  fun j i => insert (Fin.last m) ((A j i).image Fin.castSucc)

abbrev statement : Prop :=
  ∀ (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)),
    (OVHyp k t N m A ↔ IsBollobasTuple k t N (m + 1) (adjoin A))

theorem key {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (f : Fin k → Fin N) :
    kInter (adjoin A) f = insert (Fin.last m) ((kInter A f).image Fin.castSucc) := by
  ext r
  induction r using Fin.lastCases with
  | last => simp [kInter, adjoin]
  | cast s =>
      simp [kInter, adjoin, Fin.castSucc_ne_last, (Fin.castSucc_injective m).eq_iff]

theorem hcard {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (f : Fin k → Fin N) :
    (kInter (adjoin A) f).card = (kInter A f).card + 1 := by
  have hnot : Fin.last m ∉ (kInter A f).image Fin.castSucc := by
    simp [Fin.castSucc_ne_last]
  rw [key A f, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (Fin.castSucc_injective m)]

theorem proof : statement := by
  intro k t N m A
  constructor
  · intro h f
    rw [hcard A f, Nat.even_add_one, h f, not_le]
  · intro h f
    have hthis := h f
    rw [hcard A f, Nat.even_add_one] at hthis
    rw [← not_lt, ← hthis, not_not]

end Submissions.OVParityInterchange.WoshuaJolk
