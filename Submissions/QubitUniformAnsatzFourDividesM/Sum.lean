import Mathlib

namespace Submissions.QubitUniformAnsatzFourDividesM.Sum

theorem proof :
    ∀ cycles : List ℕ,
      (∀ c ∈ cycles, Even c ∧ 4 ∣ c) →
      4 ∣ cycles.foldl (· + ·) 0 := by
  intro cycles h
  have general :
      ∀ (l : List ℕ) (acc : ℕ),
        (∀ c ∈ l, 4 ∣ c) → 4 ∣ acc → 4 ∣ List.foldl (· + ·) acc l := by
    intro l
    induction l with
    | nil =>
        intro acc _ hacc
        simpa [List.foldl] using hacc
    | cons c cs ih =>
        intro acc hc hacc
        simp only [List.foldl_cons]
        refine ih (acc + c) ?_ (dvd_add hacc (hc c ?_))
        · intro x hx
          exact hc x (List.mem_cons.mpr (Or.inr hx))
        · exact List.mem_cons.mpr (Or.inl rfl)
  exact general cycles 0 (fun c hc => (h c hc).2) (dvd_zero 4)

end Submissions.QubitUniformAnsatzFourDividesM.Sum
