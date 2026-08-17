import Mathlib

/-!
# A restatement attack on `ExpLatticeHellyFinite`

Everything in this file is true and has a real proof.  It is not the statement that was
posed.  The canonical convex-position clause is

    ∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})

and this file drops the `\ {v}`:

    ∀ v ∈ V, v ∉ convexHull ℝ V

which is false for every non-empty `V`, since `V ⊆ convexHull ℝ V`.  The hypothesis is
therefore satisfiable only by `V = ∅`, `N = 0` works, and the whole open problem evaporates.
It is a one-token difference, it reads as a natural transcription of "no vertex lies in the
hull", it passes the static policy scan, and it is caught only by resolving the canonical
type by name.

Expected verdict: red, reason `restatement`.
-/

namespace Submissions.ExpLatticeHellyFinite.MalloryNoErase

theorem proof :
    ∀ α : ℝ, 1 < α →
      ∃ N : ℕ, ∀ V : Set (Fin 3 → ℝ),
        (V.Finite ∧
          V ⊆ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ∧
          (∀ v ∈ V, v ∉ convexHull ℝ V) ∧
          convexHull ℝ V ∩ {x : Fin 3 → ℝ | ∀ i, ∃ n : ℕ, x i = α ^ n} ⊆ V) →
        V.ncard ≤ N := by
  intro α _hα
  refine ⟨0, fun V hV => ?_⟩
  obtain ⟨-, -, hvert, -⟩ := hV
  have hV0 : V = ∅ :=
    Set.subset_empty_iff.mp fun v hv => absurd (subset_convexHull ℝ V hv) (hvert v hv)
  simp [hV0]

end Submissions.ExpLatticeHellyFinite.MalloryNoErase
