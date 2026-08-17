import Mathlib

/-!
# O'Neill–Verstraëte Conjecture 1 is false

The negation of the root statement of this problem, verbatim: `KWiseOddtownConj1.statement`
with a `¬` in front and nothing else changed.  The definitions below are copied character for
character from `Statements/KWiseOddtownConj1.lean`, so
`OVConj1Refuted.statement` and `¬ KWiseOddtownConj1.statement` are definitionally the same
proposition — checked by `Iff.rfl` before this file was posted.

The witness is explicit and elementary, and needs no external input.  Fix `M ≡ 0 (mod 4)` with
`M ≥ 8`, and take the ground set to be two disjoint copies of the two-element subsets of
`[M]`, plus one extra point.  Index a single family by `[M]`:

* in copy 1, `F i` holds the pairs **containing** `i`;
* in copy 2, `F i` holds the pairs **avoiding** `i`;
* the extra point lies in every `F i`.

Feed it to Conjecture 1 at `(k,t) = (6,5)` — admissible, since `2 ≤ 5 ≤ 6` and `8 < 10` — on
the diagonal `A₁ = ⋯ = A₆ = F`.  For `S` of size `d` the three parts contribute, respectively,
`M-1` / `1` / `0` (as `d = 1` / `d = 2` / `d ≥ 3`), then `(M-d).choose 2`, then `1`, so

    |⋂_{i ∈ S} F i| = c₁(d) + (M-d).choose 2 + 1

and with `M = 4K` the binomial factors as `(4K-1)(2K-1)`, `(2K-1)(4K-3)`, `(4K-3)(2K-2)`,
`(2K-2)(4K-5)`, `(4K-5)(2K-3)`, `(2K-3)(4K-7)` for `d = 1,…,6` — odd, odd, even, even, odd,
odd.  The total is therefore odd for `d ≤ 4` and even for `d = 5, 6`, which is exactly the
`(6,5)` hypothesis.  The family has `m = M` while the ground set has `n = M(M-1) + 1`, so
`m` grows like `√n` where Conjecture 1 demands `O(n^{1/3})`: `M³ ≤ C·(M(M-1)+1) ≤ C·M²`
forces `M ≤ C`, and `M := 4(C+2)` breaks it.

In the language of the α-town literature this family is an α-town for
`α = (1,1,1,1,0,0) ∈ F₂⁶`, whose Dong–Ouyang–Wei level is `2` rather than the `⌊6/2⌋ = 3` the
conjecture assumes — see `DiagonalAlphaTown65`.  Their Theorem 3 predicts that such families
of size `(1+o(1))√n` exist; the construction above exhibits one, so nothing here depends on
that unrefereed preprint.  `(6,5)` is the case O'Neill and Verstraëte name as the first open
one, and with their own Lemma 6 upper bound this pins `b_{6,5}(n) = Θ(n^{1/2})`.

Cases with `lv = ⌊k/2⌋` — including `(7,6)`, the new first open case — are untouched by this.
-/

namespace Statements.OVConj1Refuted

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

/-- The canonical proposition: Conjecture 1, under the paper's standing hypothesis
`2 ≤ t ≤ k`, is false. -/
abbrev statement : Prop :=
  ¬ (∀ k t : ℕ, 2 ≤ t → t ≤ k → k + 2 < 2 * t →
      ∃ C : ℕ, ∀ (n m : ℕ) (A : Fin k → Fin m → Finset (Fin n)),
        OVHyp k t m n A → m ^ (k / 2) ≤ C * n)

/-- The target. -/
theorem target : statement := sorry

end Statements.OVConj1Refuted
