import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
Route: one transfer lemma, used twice.

For a group action, `x ↦ k • x` is injective, so equivariance `A (k * g) = (A g).image (k • ·)`
upgrades to a membership equivalence `x ∈ A g ↔ k • x ∈ A (k * g)` (`memA`, `memB`).

* **Collapse.**  `A g = A (g * 1) = (A 1).image (g • ·)` and `B (g * d) = (B d).image (g • ·)`,
  and `Finset.image_inter` (injectivity again) turns the intersection of the two images into
  the image of the intersection.  Neither the disjointness clause nor the cross clause is
  needed, so this half is proved under strictly weaker hypotheses than the canonical type
  states — which is admissible, and recorded here deliberately.

* **Orbit-constancy.**  `g ↦ k * g` is a bijection of the two filtered index sets: `memA` gives
  `x ∈ A g ↔ k • x ∈ A (k * g)`, and `memB` together with associativity `k * (g * d) = (k * g) * d`
  gives `x ∈ B (g * d) ↔ k • x ∈ B ((k * g) * d)`.  `Finset.card_nbij'` with inverse
  `g ↦ k⁻¹ * g` closes it.  This holds for every `d`, including `d = 1`.
-/

namespace Submissions.GroupInvariantBridge.EquivariantCollapse

/-- The canonical proposition of `Statements.GroupInvariantBridge`. -/
theorem proof :
    ∀ (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X] [MulAction G X]
      (A B : G → Finset X),
      (∀ k g : G, A (k * g) = (A g).image (fun x => k • x)) →
      (∀ k g : G, B (k * g) = (B g).image (fun x => k • x)) →
      (∀ g : G, A g ∩ B g = ∅) →
      (∀ g h : G, g ≠ h → (A g ∩ B h).card = 1) →
      (∀ d : G, d ≠ 1 → ∀ g : G, A g ∩ B (g * d) = (A 1 ∩ B d).image (fun x => g • x))
        ∧ (∀ (d : G) (x : X) (k : G),
            (Finset.univ.filter (fun g : G => x ∈ A g ∧ x ∈ B (g * d))).card
              = (Finset.univ.filter (fun g : G => k • x ∈ A g ∧ k • x ∈ B (g * d))).card) := by
  intro G X _ _ _ _ _ A B hA hB _ _
  have hinj : ∀ k : G, Function.Injective (fun x : X => k • x) := fun k =>
    MulAction.injective k
  -- membership transfer along equivariance
  have memA : ∀ (k g : G) (x : X), x ∈ A g ↔ k • x ∈ A (k * g) := by
    intro k g x
    rw [hA k g]
    constructor
    · intro hx; exact Finset.mem_image_of_mem _ hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx
      rwa [hinj k hyx] at hy
  have memB : ∀ (k g : G) (x : X), x ∈ B g ↔ k • x ∈ B (k * g) := by
    intro k g x
    rw [hB k g]
    constructor
    · intro hx; exact Finset.mem_image_of_mem _ hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx
      rwa [hinj k hyx] at hy
  constructor
  · -- collapse
    intro d _ g
    have hAg : A g = (A 1).image (fun x => g • x) := by
      have := hA g 1
      rwa [mul_one] at this
    rw [hAg, hB g d, ← Finset.image_inter _ _ (hinj g)]
  · -- orbit-constancy
    intro d x k
    refine Finset.card_bij' (fun g _ => k * g) (fun g _ => k⁻¹ * g) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      refine ⟨(memA k g x).1 hg.1, ?_⟩
      have h2 : k • x ∈ B (k * (g * d)) := (memB k (g * d) x).1 hg.2
      rwa [← mul_assoc] at h2
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have h1 : x ∈ A (k⁻¹ * g) := by
        rw [memA k (k⁻¹ * g) x, ← mul_assoc, mul_inv_cancel, one_mul]; exact hg.1
      have h2 : x ∈ B (k⁻¹ * g * d) := by
        rw [memB k (k⁻¹ * g * d) x, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
        exact hg.2
      exact ⟨h1, h2⟩
    · intro g _; simp [← mul_assoc]
    · intro g _; simp [← mul_assoc]

end Submissions.GroupInvariantBridge.EquivariantCollapse
