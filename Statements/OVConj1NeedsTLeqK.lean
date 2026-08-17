import Mathlib

/-!
# Conjecture 1 as printed needs the standing hypothesis `t ≤ k`

O'Neill–Verstraëte, arXiv:2011.09402v1, page 2, Conjecture 1 opens "Let `t, k` be integers
with `t ≥ 2` and `2t − 2 > k`."  It does not repeat `t ≤ k`, which is the paper's standing
hypothesis (the abstract opens "For integers `2 ≤ t ≤ k`").  With only the printed
hypotheses the conjecture is false, and this statement exhibits the family.

`(k, t) = (3, 4)` satisfies `t ≥ 2` and `2t − 2 = 6 > 3 = k`.  Among three indices at most
three are distinct, so "at least `4` of the `i_j` are distinct" never holds and the hypothesis
degenerates to "every triple intersection is odd".  Taking `n = 1` and `A_{j,i} = [1]` gives
`|⋂| = 1`, odd, for every choice of indices and for every `m`, while `⌊3/2⌋ = 1` demands
`m = O(n)`.

`k` and `t` are **fixed at 3 and 4** rather than quantified, and the claim is stated
positively (`∀ C, ∃ …`) rather than as the negation of a universally quantified sentence.
Both choices are deliberate.  The quantified negation admits a proof with no combinatorial
content at all: `(k, t) = (1, 2)` is also admissible for the printed hypotheses, `⌊1/2⌋ = 0`,
and at `n = m = 0` the conclusion reads `0 ^ 0 = 1 ≤ C * 0 = 0`, false — a fact about `ℕ`
exponentiation, not about oddtown.  A degenerate-artifact hunter found exactly that and
closed the earlier draft with it.  Fixing `k = 3` forces `⌊k/2⌋ = 1`, and the `∃`-form forces
a proof to exhibit the family.

This does not retract the conjecture; it fixes its quantifier range.  What survives is
Conjecture 1 under the paper's standing hypothesis `2 ≤ t ≤ k`, which is the root statement of
this problem and is untouched by this.
-/

namespace Statements.OVConj1NeedsTLeqK

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, as a `Finset` of the ground set `Fin n`. -/
def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

/-- The hypothesis of Conjecture 1 at parameter `t`. -/
def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-- The canonical proposition: at `(k,t) = (3,4)` — admissible for Conjecture 1 as printed,
inadmissible under the paper's standing `t ≤ k` — no bound `m = O(n^{1/⌊k/2⌋})` holds. -/
abbrev statement : Prop :=
  ∀ C : ℕ, ∃ (n m : ℕ) (A : Fin 3 → Fin m → Finset (Fin n)),
    OVHyp 3 4 m n A ∧ ¬ (m ^ (3 / 2) ≤ C * n)

/-- The target. -/
theorem target : statement := sorry

end Statements.OVConj1NeedsTLeqK
