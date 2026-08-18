import Mathlib.Data.List.Basic

/-!
# CurrieMolMorphismAtK33 — an explicit Currie–Mol morphism at `k = 33`

Companion to `Statements.CurrieMolMorphismsAbove21`, which carries the same claim for
`k = 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60`. This statement adds `k = 33`, the first ODD alphabet size above `31` for which
a morphism has been found, and the only value the diversified search in that session reached
beyond the block already filed.

Currie–Mol (arXiv:2006.07474v1 = TCS 866 (2021) 51–63) publish `f_k` only for `k = 4,…,21`.
Their Theorem 5 needs, at each `k`, a uniform binary morphism `f_k` with the Moulin-Ollagnier
*algebraic property*

    ∃ φ ∈ S_k,  φ · τ(f(a)) · φ⁻¹ = τ(a)   for a ∈ {1,2},   where τ = σ ∘ g,

which is what promotes a finite kernel-repetition check to a statement about the infinite
word. This statement is that property, proved, for `f₃₃(1) = 121111112112121211212121111`,
`f₃₃(2) = 121111112112121211212121112` (27-uniform), with `g(1) = 31`, `g(2) = 12`.

## What is claimed, and what is not

CLAIMED: `f₃₃` is uniform, `f₃₃(1)` begins with `1`, the two blocks end in different letters,
`φ` is a permutation of `{1,…,33}` with inverse `ψ`, and `φ · τ(f₃₃(a)) · φ⁻¹ = τ(a)` for
`a ∈ {1,2}`.

NOT claimed: `URT(33) = 32/31`. The rest of Theorem 5 was run and is reported as evidence,
on the same footing as in the companion statement: the prefix `u` encoded by `g(f₃₃^m(1))` is
undirected `(32/31)⁺`-free; `312` and `322` do not occur in `g(f₃₃^ω(1))`; every factor of
`t(w)` below the length Lemma 4's bound requires occurs in `t(u)`; and the kernel-repetition
search returns ZERO candidates satisfying Currie–Mol's inequality (1), which is their `k ≥ 6`
branch.

This value is worth recording separately because an EARLIER candidate at `k = 33` was
REJECTED: it passed a 500-letter freeness filter and then failed at length 538, its decoded
word carrying an undirected `(32/31)⁺` power. The morphism below is a different one, found by
a search seeded with pinned prefixes, and it survives the full pipeline.
-/

namespace Submissions.CurrieMolMorphismAtK33.AlgProp

/-- Currie-Mol's `sigma(m)` acting on the letter `j` of `Sigma_k = {1,...,k}`: fixes
`1,...,m-1`, sends `j` to `j+1` for `m <= j <= k-1`, and sends `k` to `m`. Identical,
character for character, to `Statements.TauNormalForm.sig` and to
`Statements.MoulinOllagnierWitnessAtK22.sig`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `sigma(t_1 ... t_n)` applied to `j`. `sigma` is a morphism into `S_k` and the product is
ordinary function composition, so `sigma(t_1 ... t_n) = sigma(t_1) o ... o sigma(t_n)`: the
LAST letter acts first. -/
def act (k : ℕ) (w : List ℕ) (j : ℕ) : ℕ := w.foldr (sig k) j

/-- `g(1) = 31`, `g(2) = 12`: Currie-Mol's fixed binary-to-ternary morphism, which is their
`g_k` for every `k` outside `{5,6,8}`, hence for every `k` appearing below. -/
def gblock : ℕ → List ℕ
  | 1 => [3, 1]
  | _ => [1, 2]

/-- `g` extended to a morphism on binary words. -/
def gexp (u : List ℕ) : List ℕ := u.flatMap gblock

/-- `tau(u) = sigma(g(u))`, applied to the letter `j`. -/
def tau (k : ℕ) (u : List ℕ) (j : ℕ) : ℕ := act k (gexp u) j

/-- The letters `Sigma_k = {1,...,k}`. -/
def pts (k : ℕ) : List ℕ := (List.range k).map (· + 1)

/-- A permutation given as a lookup table indexed by the letter, with `0` off-range. -/
def app (P : List ℕ) (j : ℕ) : ℕ := P.getD j 0

/-- One row: the alphabet size `k`, the blocks `f_k(1)`, `f_k(2)`, the conjugator `phi_k`
and its inverse `psi_k`, the last two as lookup tables (entry `0` is padding, so entry `j`
is the image of the letter `j`). -/
abbrev Row : Type := ℕ × List ℕ × List ℕ × List ℕ × List ℕ

/-- What a row asserts. `f_k` is uniform, `f_k(1)` begins with `1`, and the two blocks end in
different letters -- Currie-Mol's unique-cut side conditions. `phi_k` maps the letters into
the letters and `psi_k` is a two-sided inverse for it there, so `phi_k` is a permutation of
`Sigma_k`. And on every letter `phi_k o tau(f_k(a)) = tau(a) o phi_k`, which is exactly
Moulin-Ollagnier's algebraic property `phi_k . tau(f_k(a)) . phi_k^{-1} = tau(a)` for
`a` in `{1,2}`. -/
abbrev Good (k : ℕ) (F1 F2 P Q : List ℕ) : Prop :=
  F1.length = F2.length ∧
  F1.head? = some 1 ∧
  F1.getLast? ≠ F2.getLast? ∧
  ∀ j ∈ pts k,
    1 ≤ app P j ∧ app P j ≤ k ∧
    app Q (app P j) = j ∧
    app P (app Q j) = j ∧
    app P (tau k F1 j) = tau k [1] (app P j) ∧
    app P (tau k F2 j) = tau k [2] (app P j)

/-- The table: one row per alphabet size. -/
def table : List Row :=
  [(33, [1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1], [1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2], [0, 26, 11, 20, 14, 27, 21, 8, 5, 2, 15, 30, 24, 31, 25, 18, 9, 12, 19, 6, 1, 3, 13, 28, 29, 22, 23, 16, 4, 10, 17, 7, 33, 32], [0, 20, 9, 21, 28, 8, 19, 31, 7, 16, 29, 2, 17, 22, 4, 10, 27, 30, 15, 18, 3, 6, 25, 26, 12, 14, 1, 5, 23, 24, 11, 13, 33, 32])]

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Every row of the table carries Moulin-Ollagnier's algebraic property. -/
theorem proof : ∀ e ∈ table, Good e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 := by decide

end Submissions.CurrieMolMorphismAtK33.AlgProp
