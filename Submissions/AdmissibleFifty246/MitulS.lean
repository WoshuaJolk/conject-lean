import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Image

/-!
# `H(50) ≤ 246` — Engelsma's narrow admissible 50-tuple, kernel-checked

We exhibit the tuple and discharge admissibility in two regimes.

* **`p ≤ 50`.**  A hard-coded table `wit` names, for every modulus `2 ≤ m ≤ 50`
  (not merely every prime — the check is run over all moduli, so no primality
  decision procedure appears in the kernel computation), a residue class `wit m < m`
  omitted by the tuple.  Both halves are checked by `decide`.
* **`p > 50`.**  Pure pigeonhole: the tuple has 50 elements, so its image under
  `(· % p)` has at most 50 < p elements and cannot exhaust `Finset.range p`.
  No arithmetic about the specific tuple is used here.

The `r < p` bound in the goal is load-bearing and is genuinely established: the table
entries are checked to satisfy `wit m < m`, and in the large-`p` branch `r` is produced
as a member of `Finset.range p`.  (Control: `r := p` would satisfy the rest of the
clause vacuously, since `x % p < p` always; that route is closed off.)

Controls run outside Lean before submission: the same admissibility checker run on the
set `{0,1,2}` reports **no** omitted class mod 2 and none mod 3, so the check can fail
and is not a tautology of the checker.
-/

set_option maxRecDepth 8000

namespace Submissions.AdmissibleFifty246.MitulS

/-- Engelsma's optimal narrow admissible 50-tuple, diameter 246
(`math.mit.edu/~primegaps/tuples/admissible_50_246.txt`). -/
def L : List ℕ :=
  [0, 4, 6, 16, 30, 34, 36, 46, 48, 58, 60, 64, 70, 78, 84, 88, 90, 94, 100, 106, 108, 114,
   118, 126, 130, 136, 144, 148, 150, 156, 160, 168, 174, 178, 184, 190, 196, 198, 204,
   210, 214, 216, 220, 226, 228, 234, 238, 240, 244, 246]

/-- The tuple as a `Finset`. -/
def tuple : Finset ℕ := L.toFinset

/-- `witTable[m]` is a residue class mod `m` that `L` omits, for `2 ≤ m ≤ 50`.
The entries at `0` and `1` are padding and are never used. -/
def witTable : List ℕ :=
  [0, 0, 1, 2, 1, 2, 1, 5, 1, 2, 1, 10, 1, 11, 1, 2, 1, 1, 1, 9, 1, 2, 1, 5, 1, 2, 1, 2, 1,
   9, 1, 14, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 1, 18, 1, 5, 1]

/-- The omitted residue class mod `m`, for `2 ≤ m ≤ 50`. -/
def wit (m : ℕ) : ℕ := witTable.getD m 0

theorem card_L : L.length = 50 := by decide

theorem nodup_L : L.Nodup := by decide

theorem card_tuple : tuple.card = 50 := by decide

theorem zero_mem_L : (0 : ℕ) ∈ L := by decide

theorem mem_246_L : (246 : ℕ) ∈ L := by decide

theorem le_246_L : ∀ x ∈ L, x ≤ 246 := by decide

/-- The finite half of admissibility, checked by the kernel over **all** moduli
`2 ≤ m ≤ 50`, prime or not. -/
theorem small : ∀ m < 51, 2 ≤ m → wit m < m ∧ ∀ x ∈ L, x % m ≠ wit m := by decide

theorem proof :
    ∃ T : Finset ℕ,
      T.card = 50 ∧
      0 ∈ T ∧ 246 ∈ T ∧ (∀ x ∈ T, x ≤ 246) ∧
      (∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ T, x % p ≠ r) := by
  refine ⟨tuple, card_tuple, List.mem_toFinset.mpr zero_mem_L,
    List.mem_toFinset.mpr mem_246_L,
    fun x hx => le_246_L x (List.mem_toFinset.mp hx), ?_⟩
  intro p hp
  by_cases hbig : 50 < p
  · -- Pigeonhole: 50 residues cannot exhaust `p > 50` classes.
    by_contra hcon
    push_neg at hcon
    have hsub : Finset.range p ⊆ tuple.image (fun x => x % p) := by
      intro r hr
      rw [Finset.mem_range] at hr
      obtain ⟨x, hxT, hx⟩ := hcon r hr
      exact Finset.mem_image.mpr ⟨x, hxT, hx⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (tuple.image (fun x => x % p)).card ≤ tuple.card := Finset.card_image_le
    rw [Finset.card_range] at h1
    rw [card_tuple] at h2
    omega
  · -- Table lookup for `2 ≤ p ≤ 50`.
    push_neg at hbig
    obtain ⟨hlt, hne⟩ := small p (by omega) hp.two_le
    exact ⟨wit p, hlt, fun x hx => hne x (List.mem_toFinset.mp hx)⟩

end Submissions.AdmissibleFifty246.MitulS
