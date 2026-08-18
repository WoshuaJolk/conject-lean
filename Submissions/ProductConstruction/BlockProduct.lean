import Mathlib
import Commons.SetPairSystem

/-!
Proof of `Statements.ProductConstruction.statement` (Füredi–Gyárfás–Király Proposition 1.1).
The ground set of the outer system is embedded in the evens, and the `i`-th disjoint copy of
the inner system in the odds via `Nat.pair i`; the cross intersection then picks up exactly
one witness, the inner one when the block indices agree and the outer one when they differ.
-/

namespace Submissions.ProductConstruction.BlockProduct


open Finset

/-- Ground elements of the outer (block-level) system land on the even naturals. -/
def out (e : ℕ) : ℕ := 2 * e

/-- Ground element `x` of the `i`-th disjoint copy of the inner system lands on an odd
natural; `Nat.pair` keeps distinct copies apart. -/
def inn (i x : ℕ) : ℕ := 2 * Nat.pair i x + 1

lemma pair_eq {i x i' y : ℕ} (h : Nat.pair i x = Nat.pair i' y) : (i, x) = (i', y) := by
  have := congrArg Nat.unpair h
  rwa [Nat.unpair_pair, Nat.unpair_pair] at this

lemma out_inj : Function.Injective out := by
  intro x y h
  simp only [out] at h
  omega

lemma inn_inj (i : ℕ) : Function.Injective (inn i) := by
  intro x y h
  simp only [inn] at h
  have h2 : Nat.pair i x = Nat.pair i y := by omega
  exact congrArg Prod.snd (pair_eq h2)

lemma inn_ne_out (i x e : ℕ) : inn i x ≠ out e := by
  simp only [inn, out]; omega

lemma inn_ne_inn {i i' : ℕ} (h : i ≠ i') (x y : ℕ) : inn i x ≠ inn i' y := by
  intro hc
  simp only [inn] at hc
  have h2 : Nat.pair i x = Nat.pair i' y := by omega
  exact h (congrArg Prod.fst (pair_eq h2))

section
variable {m1 m2 : ℕ}

/-- Inner index of `k`. -/
def p1 (k : Fin (m1 * m2)) : Fin m1 := (finProdFinEquiv.symm k).1
/-- Outer (block) index of `k`. -/
def p2 (k : Fin (m1 * m2)) : Fin m2 := (finProdFinEquiv.symm k).2

lemma p_inj {k k' : Fin (m1 * m2)} (h : p1 k = p1 k') (h' : p2 k = p2 k') : k = k' := by
  have hp : finProdFinEquiv.symm k = finProdFinEquiv.symm k' := Prod.ext h h'
  exact finProdFinEquiv.symm.injective hp

/-- The product family. -/
def PA (A1 : Fin m1 → Finset ℕ) (A2 : Fin m2 → Finset ℕ) (k : Fin (m1 * m2)) : Finset ℕ :=
  (A1 (p1 k)).image (inn (p2 k).val) ∪ (A2 (p2 k)).image out

lemma mem_PA {A1 : Fin m1 → Finset ℕ} {A2 : Fin m2 → Finset ℕ} {k : Fin (m1 * m2)} {z : ℕ} :
    z ∈ PA A1 A2 k ↔
      (∃ x ∈ A1 (p1 k), inn (p2 k).val x = z) ∨ (∃ e ∈ A2 (p2 k), out e = z) := by
  simp [PA, Finset.mem_union, Finset.mem_image]

lemma card_PA_le {A1 : Fin m1 → Finset ℕ} {A2 : Fin m2 → Finset ℕ} {a1 a2 : ℕ}
    (h1 : ∀ j, (A1 j).card ≤ a1) (h2 : ∀ i, (A2 i).card ≤ a2) (k : Fin (m1 * m2)) :
    (PA A1 A2 k).card ≤ a1 + a2 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  exact Nat.add_le_add (le_trans Finset.card_image_le (h1 _))
                       (le_trans Finset.card_image_le (h2 _))

lemma inter_eq {A1 B1 : Fin m1 → Finset ℕ} {A2 B2 : Fin m2 → Finset ℕ}
    (k k' : Fin (m1 * m2)) (hii : p2 k = p2 k') :
    PA A1 A2 k ∩ PA B1 B2 k' =
      ((A1 (p1 k) ∩ B1 (p1 k')).image (inn (p2 k').val))
        ∪ ((A2 (p2 k) ∩ B2 (p2 k')).image out) := by
  ext z
  simp only [Finset.mem_inter, mem_PA, Finset.mem_union, Finset.mem_image, hii]
  constructor
  · rintro ⟨hl, hr⟩
    rcases hl with ⟨x, hx, hxz⟩ | ⟨e, he, hez⟩
    · rcases hr with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
      · have hxy : x = y := inn_inj _ (by rw [hxz, hyz])
        refine Or.inl ⟨x, ⟨hx, ?_⟩, hxz⟩
        rw [hxy]; exact hy
      · exact absurd (hxz.trans hfz.symm) (inn_ne_out _ _ _)
    · rcases hr with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
      · exact absurd (hyz.trans hez.symm) (inn_ne_out _ _ _)
      · have hef : e = f := out_inj (by rw [hez, hfz])
        refine Or.inr ⟨e, ⟨he, ?_⟩, hez⟩
        rw [hef]; exact hf
  · rintro (⟨x, hx, hxz⟩ | ⟨e, he, hez⟩)
    · exact ⟨Or.inl ⟨x, hx.1, hxz⟩, Or.inl ⟨x, hx.2, hxz⟩⟩
    · exact ⟨Or.inr ⟨e, he.1, hez⟩, Or.inr ⟨e, he.2, hez⟩⟩

lemma inter_eq_ne {A1 B1 : Fin m1 → Finset ℕ} {A2 B2 : Fin m2 → Finset ℕ}
    (k k' : Fin (m1 * m2)) (hii : p2 k ≠ p2 k') :
    PA A1 A2 k ∩ PA B1 B2 k' = (A2 (p2 k) ∩ B2 (p2 k')).image out := by
  have hne : (p2 k).val ≠ (p2 k').val := fun hc => hii (Fin.val_injective hc)
  ext z
  simp only [Finset.mem_inter, mem_PA, Finset.mem_image]
  constructor
  · rintro ⟨hl, hr⟩
    rcases hl with ⟨x, hx, hxz⟩ | ⟨e, he, hez⟩
    · rcases hr with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
      · exact absurd (hxz.trans hyz.symm) (inn_ne_inn hne _ _)
      · exact absurd (hxz.trans hfz.symm) (inn_ne_out _ _ _)
    · rcases hr with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
      · exact absurd (hyz.trans hez.symm) (inn_ne_out _ _ _)
      · have hef : e = f := out_inj (by rw [hez, hfz])
        refine ⟨e, ⟨he, ?_⟩, hez⟩
        rw [hef]; exact hf
  · rintro ⟨e, he, hez⟩
    exact ⟨Or.inr ⟨e, he.1, hez⟩, Or.inr ⟨e, he.2, hez⟩⟩

end

/-- Füredi–Gyárfás–Király Proposition 1.1: 1-cross intersecting set pair systems multiply. -/
theorem product {a1 b1 m1 a2 b2 m2 : ℕ}
    {A1 B1 : Fin m1 → Finset ℕ} {A2 B2 : Fin m2 → Finset ℕ}
    (h1 : Commons.OneCrossSPS a1 b1 m1 A1 B1)
    (h2 : Commons.OneCrossSPS a2 b2 m2 A2 B2) :
    ∃ A B : Fin (m1 * m2) → Finset ℕ,
      Commons.OneCrossSPS (a1 + a2) (b1 + b2) (m1 * m2) A B := by
  obtain ⟨hA1, hB1, hd1, hc1⟩ := h1
  obtain ⟨hA2, hB2, hd2, hc2⟩ := h2
  refine ⟨PA A1 A2, PA B1 B2, fun k => card_PA_le hA1 hA2 k,
          fun k => card_PA_le hB1 hB2 k, ?_, ?_⟩
  · intro k
    rw [inter_eq k k rfl, hd1 (p1 k), hd2 (p2 k)]
    simp
  · intro k k' hkk'
    by_cases hii : p2 k = p2 k'
    · have hjj : p1 k ≠ p1 k' := fun hc => hkk' (p_inj hc hii)
      have h0 : A2 (p2 k) ∩ B2 (p2 k') = ∅ := by rw [← hii]; exact hd2 (p2 k)
      rw [inter_eq k k' hii, h0, Finset.image_empty, Finset.union_empty,
          Finset.card_image_of_injective _ (inn_inj _)]
      exact hc1 _ _ hjj
    · rw [inter_eq_ne k k' hii, Finset.card_image_of_injective _ out_inj]
      exact hc2 _ _ hii

/-- Swapping the two families of a 1-cross intersecting SPS swaps the two bounds. -/
theorem swap {a b m : ℕ} {A B : Fin m → Finset ℕ} (h : Commons.OneCrossSPS a b m A B) :
    Commons.OneCrossSPS b a m B A := by
  obtain ⟨hA, hB, hd, hc⟩ := h
  refine ⟨hB, hA, ?_, ?_⟩
  · intro i
    rw [Finset.inter_comm]
    exact hd i
  · intro i j hij
    rw [Finset.inter_comm]
    exact hc j i (Ne.symm hij)

/-- Squaring an asymmetric block. Any `(a,b)`-bounded 1-cross intersecting SPS of size `m`
produces an `(a+b, a+b)`-bounded one of size `m^2`, by multiplying the system with its own
mirror image. -/
theorem square {a b m : ℕ} {A B : Fin m → Finset ℕ} (h : Commons.OneCrossSPS a b m A B) :
    ∃ A' B' : Fin (m * m) → Finset ℕ,
      Commons.OneCrossSPS (a + b) (a + b) (m * m) A' B' := by
  obtain ⟨A', B', hA'⟩ := product h (swap h)
  rw [Nat.add_comm b a] at hA'
  exact ⟨A', B', hA'⟩



/-- The submitted declaration. -/
theorem proof : ∀ (a₁ b₁ m₁ a₂ b₂ m₂ : ℕ) (A₁ B₁ : Fin m₁ → Finset ℕ) (A₂ B₂ : Fin m₂ → Finset ℕ),
    Commons.OneCrossSPS a₁ b₁ m₁ A₁ B₁ →
    Commons.OneCrossSPS a₂ b₂ m₂ A₂ B₂ →
      ∃ A B : Fin (m₁ * m₂) → Finset ℕ,
        Commons.OneCrossSPS (a₁ + a₂) (b₁ + b₂) (m₁ * m₂) A B :=
  fun _ _ _ _ _ _ _ _ _ _ h1 h2 => product h1 h2

end Submissions.ProductConstruction.BlockProduct
