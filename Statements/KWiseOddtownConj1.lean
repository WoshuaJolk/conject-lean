import Mathlib

/-!
# O'Neill–Verstraëte, Conjecture 1 (Graphs and Combinatorics 38 (2022), Paper 101)

Source: J. O'Neill and J. Verstraëte, *A note on k-wise oddtown problems*,
arXiv:2011.09402v1, page 2, Conjecture 1; published as Graphs and Combinatorics 38 (2022),
Paper 101.  Verbatim:

> **Conjecture 1.** Let `t, k` be integers with `t ≥ 2` and `2t − 2 > k`.  If
> `(A₁, A₂, …, A_k)` are set families of an `n` element set with `A_j = {A_{j,i} : 1 ≤ i ≤ m}`
> where `|⋂_{j=1}^{k} A_{j,i_j}|` is even if and only if at least `t` of the `i_j` are
> distinct, then `m = O(n^{1/⌊k/2⌋})`.

Two deliberate, documented departures from the printed line, both recorded in the problem's
`scope`:

* **`t ≤ k` is added.**  It is the paper's standing hypothesis — the abstract opens "For
  integers `2 ≤ t ≤ k`", and the sentence introducing the conjecture reads "When `t < k` and
  `2t − 2 > k`, we are able to show that `m = O(n^{1/(k−t+1)})`, and conjecture that a
  stronger bound holds".  Without it the printed line is *false*: at `(k,t) = (3,4)` the
  hypothesis "even iff at least `4` of the `3` indices are distinct" says every triple
  intersection is odd, which `A_{j,i} = [n]` with `n` odd satisfies for every `m`.  That
  refutation is filed separately.
* **`O(n^{1/⌊k/2⌋})` is spelled `m ^ ⌊k/2⌋ ≤ C * n`.**  For `C ≥ 0` these are equivalent
  (`m ≤ C·n^{1/d} ↔ m^d ≤ C^d·n`, and `C` is existentially quantified), and this spelling
  keeps the statement inside `ℕ`, with no real powers and no `Filter.Tendsto` scaffolding.
  `k / 2` is `ℕ` division, i.e. `⌊k/2⌋`; the hypotheses force `k ≥ 2`, so the exponent is
  positive.

Note the quantifier order: `C` may depend on `k` and `t` but not on `n`, `m` or the families.
No hypothesis `1 ≤ n` is needed — at `n = 0` and `m ≥ 1` the constant map `f` has
`|image f| = 1 < 2 ≤ t` while `|⋂| = 0` is even, so `OVHyp` already fails.
-/

namespace Statements.KWiseOddtownConj1

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, as a `Finset` of the ground set `Fin n`. -/
def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

/-- The hypothesis of Conjecture 1 at parameter `t`, for `k` families `A_j = {A_{j,i}}`
indexed by `i ∈ [m]` inside the ground set `[n]`: the size of `A_{1,i₁} ∩ ⋯ ∩ A_{k,i_k}` is
even if and only if at least `t` of the indices `i₁, …, i_k` are distinct. -/
def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  ∀ k t : ℕ, 2 ≤ t → t ≤ k → k + 2 < 2 * t →
    ∃ C : ℕ, ∀ (n m : ℕ) (A : Fin k → Fin m → Finset (Fin n)),
      OVHyp k t m n A → m ^ (k / 2) ≤ C * n

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.KWiseOddtownConj1
