import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# EmptyPolytopeFourPointCriterion

A finite set `V` of points of a set `S` in `ℝ³` is (the vertex set of) a convex polytope
empty in `S` **iff every subset of `V` with at most four elements is**.

This is what makes the whole problem finitely searchable.  Emptiness as ABFJN define it is a
global condition: it quantifies over the convex hull of `V`, and over all of `S`.  The
criterion below replaces it by a condition on subsets of size at most `4 = 3 + 1`, so
"empty" becomes an independence condition in a hypergraph whose edges are precomputable, and
an exhaustive search over empty subsets of a finite grid becomes a finite, complete
computation instead of a heuristic.

Both directions are needed and both are cheap.  Left to right is Carathéodory: a point of
`conv V` lies in the hull of an affinely independent subset, which in `ℝ³` has at most `4`
elements; if that subset is empty in `S` then the point is one of its own members.  Right to
left is heredity: every subset of an empty polytope is one, because a captured point would
have to be a non-vertex of the larger hull.

The bound `4` is `finrank ℝ (Fin 3 → ℝ) + 1`; the same statement holds in `ℝ^d` with `d + 1`.
-/

namespace Submissions.EmptyPolytopeFourPointCriterion.ViaCaratheodory

def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

theorem card_le_four {t : Finset (Fin 3 → ℝ)}
    (h : AffineIndependent ℝ ((↑) : t → (Fin 3 → ℝ))) : t.card ≤ 4 := by
  have h1 := h.card_le_finrank_succ
  rw [Fintype.card_coe] at h1
  have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → (Fin 3 → ℝ)))) ≤ 3 := by
    have h3 := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → (Fin 3 → ℝ))))
    simpa using h3
  omega

theorem hereditary {S V : Set (Fin 3 → ℝ)} (hV : IsEmptyPolytope S V)
    {W : Set (Fin 3 → ℝ)} (hWV : W ⊆ V) : IsEmptyPolytope S W := by
  obtain ⟨hVf, hVS, hVpos, hVemp⟩ := hV
  refine ⟨hVf.subset hWV, hWV.trans hVS, ?_, ?_⟩
  · intro w hw hmem
    refine hVpos w (hWV hw) (convexHull_mono ?_ hmem)
    exact Set.sdiff_subset_sdiff_left hWV
  · rintro q ⟨hq, hqS⟩
    have hqV : q ∈ V := hVemp ⟨convexHull_mono hWV hq, hqS⟩
    by_contra hqW
    refine hVpos q hqV (convexHull_mono ?_ hq)
    intro x hx
    refine ⟨hWV hx, ?_⟩
    intro he
    exact hqW (he ▸ hx)

theorem main (S V : Set (Fin 3 → ℝ)) (hVf : V.Finite) (hVS : V ⊆ S)
    (h : ∀ W, W ⊆ V → W.ncard ≤ 4 → IsEmptyPolytope S W) : IsEmptyPolytope S V := by
  refine ⟨hVf, hVS, ?_, ?_⟩
  · intro v hv hmem
    rw [convexHull_eq_union] at hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨t, hts, hai, hvt⟩ := hmem
    have hcard : (↑t : Set (Fin 3 → ℝ)).ncard ≤ 4 := by
      rw [Set.ncard_coe_finset]; exact card_le_four hai
    obtain ⟨-, -, -, hemp⟩ := h _ (hts.trans Set.sdiff_subset) hcard
    exact (hts (hemp ⟨hvt, hVS hv⟩)).2 rfl
  · rintro q ⟨hq, hqS⟩
    rw [convexHull_eq_union] at hq
    simp only [Set.mem_iUnion] at hq
    obtain ⟨t, hts, hai, hqt⟩ := hq
    have hcard : (↑t : Set (Fin 3 → ℝ)).ncard ≤ 4 := by
      rw [Set.ncard_coe_finset]; exact card_le_four hai
    obtain ⟨-, -, -, hemp⟩ := h _ hts hcard
    exact hts (hemp ⟨hqt, hqS⟩)

theorem criterion (S V : Set (Fin 3 → ℝ)) (hVf : V.Finite) (hVS : V ⊆ S) :
    (∀ W, W ⊆ V → W.ncard ≤ 4 → IsEmptyPolytope S W) ↔ IsEmptyPolytope S V :=
  ⟨main S V hVf hVS, fun hV _ hWV _ => hereditary hV hWV⟩

/-- **Emptiness is decided by the subsets of size at most four.** -/
theorem proof :
    ∀ (S V : Set (Fin 3 → ℝ)), V.Finite → V ⊆ S →
      ((∀ W, W ⊆ V → W.ncard ≤ 4 → IsEmptyPolytope S W) ↔ IsEmptyPolytope S V) :=
  criterion

end Submissions.EmptyPolytopeFourPointCriterion.ViaCaratheodory
