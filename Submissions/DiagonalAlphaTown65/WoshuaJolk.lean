import Mathlib

/-!
# Proof of `Statements.DiagonalAlphaTown65.statement`

The two sides of the `↔` are the same family of parity conditions read through two different
index objects: a function `f : Fin 6 → Fin m` on the left, the Finset `s = image f univ` of its
values on the right.  The bridge is `kInter (fun _ i => F i) f = interOn F (image f univ)`:
a point lies in `F (f j)` for every `j` exactly when it lies in `F i` for every value `i` of `f`.

For `←` (assume the `s`-form, derive the `f`-form) instantiate at `s := image f univ`, whose
card is between `1` (the image of the nonempty `Fin 6` is nonempty) and `6` (`card_image_le`).
For `→` one must realise each `s` with `1 ≤ s.card ≤ 6` as `image f univ`: enumerate `s` by
`s.equivFin.symm` and pad the enumeration out to arity `6` by repeating the last element,
i.e. `f j := s.equivFin.symm ⟨min j.val (s.card - 1), _⟩`.

`Function.Injective F` is not needed for this bridge and is ignored.

The definitions are restated rather than imported, because canonical statements carry `sorry`
and submissions may not import them.
-/

namespace Submissions.DiagonalAlphaTown65.WoshuaJolk

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, as a `Finset` of the ground set `Fin n`. -/
def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

/-- The hypothesis of Conjecture 1 at parameter `t`. -/
def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-- `⋂_{i ∈ s} F i`, the intersection of the members of `F` indexed by `s`. -/
def interOn {m n : ℕ} (F : Fin m → Finset (Fin n)) (s : Finset (Fin m)) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ i ∈ s, x ∈ F i)

/-- The bridge: intersecting along a map `f` out of `Fin 6` is intersecting over its image. -/
private theorem kInter_eq_interOn {m n : ℕ} (F : Fin m → Finset (Fin n)) (f : Fin 6 → Fin m) :
    kInter (fun _ i => F i) f = interOn F (image f univ) := by
  ext x
  simp only [kInter, interOn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  aesop

/-- Every `s` with `1 ≤ s.card ≤ 6` is the image of some `f : Fin 6 → Fin m`: enumerate `s`
and repeat the last element to pad the enumeration out to arity `6`. -/
private theorem exists_image_eq {m : ℕ} (s : Finset (Fin m)) (h1 : 1 ≤ s.card)
    (h6 : s.card ≤ 6) : ∃ f : Fin 6 → Fin m, image f univ = s := by
  classical
  have hlt : ∀ j : Fin 6, min j.val (s.card - 1) < s.card := by
    intro j; omega
  refine ⟨fun j => (s.equivFin.symm ⟨min j.val (s.card - 1), hlt j⟩).1, ?_⟩
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact (s.equivFin.symm _).2
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hi6 : (s.equivFin ⟨x, hx⟩).val < 6 := lt_of_lt_of_le (s.equivFin ⟨x, hx⟩).isLt h6
    refine ⟨⟨(s.equivFin ⟨x, hx⟩).val, hi6⟩, ?_⟩
    have heq : (⟨min (s.equivFin ⟨x, hx⟩).val (s.card - 1), hlt ⟨_, hi6⟩⟩ : Fin s.card)
        = s.equivFin ⟨x, hx⟩ := by
      apply Fin.ext
      have := (s.equivFin ⟨x, hx⟩).isLt
      simp only
      omega
    rw [heq]
    simp

/-- The target. -/
theorem proof :
  ∀ (m n : ℕ) (F : Fin m → Finset (Fin n)), Function.Injective F →
    (OVHyp 6 5 m n (fun _ i => F i) ↔
      ∀ s : Finset (Fin m), 1 ≤ s.card → s.card ≤ 6 →
        (Even (interOn F s).card ↔ 5 ≤ s.card))
    := by
  intro m n F _hF
  constructor
  · intro hOV s hs1 hs6
    obtain ⟨f, hf⟩ := exists_image_eq s hs1 hs6
    have h := hOV f
    rw [kInter_eq_interOn F f, hf] at h
    exact h
  · intro hst f
    rw [kInter_eq_interOn F f]
    have h1 : 1 ≤ (image f univ).card :=
      Finset.card_pos.mpr ⟨f 0, Finset.mem_image_of_mem f (mem_univ 0)⟩
    have h6 : (image f univ).card ≤ 6 :=
      le_trans Finset.card_image_le (by simp)
    exact hst _ h1 h6

end Submissions.DiagonalAlphaTown65.WoshuaJolk
