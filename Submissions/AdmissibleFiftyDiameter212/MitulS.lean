import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic

/-!
`H(50) ≥ 212`.  Admissibility at `p = 2, 3, 5, 7` confines an admissible `T` to the
survivors of four deleted residue classes; the kernel checks that all 210 choices of those
classes leave at most 49 survivors in `{0, …, 211}`, so a 50-element `T` cannot fit.

Controls, each confirmed to break the build before submission: raising the target to
`213 ≤ d` fails (212 is exactly where the `p ≤ 7` argument stops — some choice does leave
50 survivors at `d = 212`); tightening the survivor bound to `≤ 48` fails; dropping `p = 7`
from the four instantiations fails. Cross-check outside Lean: Engelsma's actual admissible
50-tuple has `(r₂,r₃,r₅,r₇) = (1,2,2,5)`, which leaves 49 survivors in `{0,…,211}` and 59 in
`{0,…,246}` — consistent with, and not contradicted by, this bound.
-/

set_option maxRecDepth 100000

namespace Submissions.AdmissibleFiftyDiameter212.MitulS

/-- Survivors in `{0, …, 211}` of deleting the class `rₚ` mod `p` for `p = 2, 3, 5, 7`. -/
def S (r2 r3 r5 r7 : ℕ) : Finset ℕ :=
  (Finset.range 212).filter (fun x => x % 2 ≠ r2 ∧ x % 3 ≠ r3 ∧ x % 5 ≠ r5 ∧ x % 7 ≠ r7)

/-- All 210 choices of deleted classes leave at most 49 survivors. -/
theorem check : ∀ r2 < 2, ∀ r3 < 3, ∀ r5 < 5, ∀ r7 < 7, (S r2 r3 r5 r7).card ≤ 49 := by decide

theorem main (T : Finset ℕ) (d : ℕ) (hcard : T.card = 50)
    (hadm : ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r)
    (hd : ∀ x ∈ T, x ≤ d) : 212 ≤ d := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨r2, h2, k2⟩ := hadm 2 Nat.prime_two
  obtain ⟨r3, h3, k3⟩ := hadm 3 Nat.prime_three
  obtain ⟨r5, h5, k5⟩ := hadm 5 Nat.prime_five
  obtain ⟨r7, h7, k7⟩ := hadm 7 Nat.prime_seven
  have hsub : T ⊆ S r2 r3 r5 r7 := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_range]
    have hxd := hd x hx
    exact ⟨by omega, k2 x hx, k3 x hx, k5 x hx, k7 x hx⟩
  have hle := Finset.card_le_card hsub
  have hc := check r2 h2 r3 h3 r5 h5 r7 h7
  omega

theorem proof :
    (∀ (T : Finset ℕ) (d : ℕ),
        T.card = 50 →
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) →
        (∀ x ∈ T, x ≤ d) →
        212 ≤ d)
    ∧ ¬ ∃ T : Finset ℕ,
          T.card = 50 ∧ (∀ x ∈ T, x ≤ 211) ∧
          (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) := by
  refine ⟨fun T d hc ha hd => main T d hc ha hd, ?_⟩
  rintro ⟨T, hc, hd, ha⟩
  have := main T 211 hc ha hd
  omega

end Submissions.AdmissibleFiftyDiameter212.MitulS
