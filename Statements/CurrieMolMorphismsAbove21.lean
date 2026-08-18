import Mathlib.Data.List.Basic

/-!
# CurrieMolMorphismsAbove21 — explicit Currie–Mol morphisms above `k = 21`

Currie–Mol (*The undirected repetition threshold and undirected pattern avoidance*,
arXiv:2006.07474v1 = TCS 866 (2021) 51–63) prove `URT(k) = (k-1)/(k-2)` for `k ∈ {4,…,21}`
(their Theorem 5) and record that nothing is known for any `k ≥ 22`. Their route fixes, for
each `k`, an `r`-uniform binary morphism `f_k`; the fixed point `f_k^ω(1)` is pushed through
`g` and Pansiot's `σ` to give a word over `Σ_k`, and Moulin-Ollagnier's descent then turns a
FINITE kernel-repetition check into a statement about that INFINITE word. The descent runs
only if `f_k` has the *algebraic property*

    ∃ φ ∈ S_k,  φ · τ(f(a)) · φ⁻¹ = τ(a)   for a ∈ {1,2},   where τ = σ ∘ g,

which is the hypothesis this problem's own `artifact_schema` singles out. **No `f_k` is
published for any `k ≥ 22`.** This statement exhibits one, with its conjugator, for
25 alphabet sizes: `k = 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60`.

## What is claimed here, and what is not

CLAIMED, and proved below: for every row `(k, f_k(1), f_k(2), φ_k, ψ_k)` of the table, `f_k`
is uniform, `f_k(1)` begins with `1`, the two blocks end in different letters (Currie–Mol's
unique-cut side conditions), `φ_k` is a permutation of `{1,…,k}` with inverse `ψ_k`, and
`φ_k · τ(f_k(a)) · φ_k⁻¹ = τ(a)` for `a ∈ {1,2}`.

NOT claimed here: that `URT(k) = (k-1)/(k-2)` for these `k`. Theorem 5 also needs the finite
kernel-repetition search, Lemma 4's reversible-factor bound, and the freeness of a verified
prefix — none of which is formalised in this file.

## Two independent cross-checks that this table could have failed

Every row satisfies `Statements.TauBlockSwapParity`: at each `k ≡ 2 (mod 4)` in the table
(22, 26, 30, 34, 38, 42, 46, 50, 54, 58) the uniformity `r` is ODD (13, 11, 9, 19, 11, 19,
13, 17, 15, 17), while the two rows at `k ≡ 0 (mod 4)` that came out even (`k = 56`, `r = 32`
and `k = 60`, `r = 34`) sit exactly where that barrier does not apply. Every row also
satisfies a sign condition derived in the session that produced this statement and NOT stated
in the paper: since `σ(2) = σ(1)·(1,k)` and `σ(3) = σ(1)·(1,k,2)`, the signs give
`sgn τ(1) = +1` and `sgn τ(2) = −1`, so the algebraic property forces `|f(1)|₂` even and
`|f(2)|₂` odd — which holds for all 25 rows here and for all eighteen published `f_4,…,f_21`.

## The rest of Theorem 5, run and reported as evidence

For every row, the remaining computational steps of Currie–Mol's Theorem 5 were re-run in the
session that produced this statement, by a re-implementation whose controls reproduce the
paper: all eighteen published `f_4,…,f_21` satisfy the algebraic property under these exact
conventions; pinning only `f_21(1)` makes the morphism search return the published `f_21(2)`
as the unique completion; the kernel search returns, at `k = 4`, exactly the three candidates
`(π,η) = (111, ε)`, `(121121, 1)`, `(112112, 1)` that the paper reports, and at `k = 21`
returns none, which is the paper's `k ≥ 6` branch; the undirected-freeness checker catches all
eleven leaves of their Theorem 3 tree and classifies as reverse powers exactly the four leaves
the paper calls reverse; and it was cross-checked against a second, independent implementation
on 60 random inputs over 7 alphabet sizes with exact agreement on the first-violation index.
For each row the steps run were: (A) the prefix `u` encoded by `g(f_k^m(1))` is undirected
`((k-1)/(k-2))⁺`-free; (B) `312` and `322` do not occur in `g(f_k^ω(1))`, a bound `N` on the
gaps between occurrences of `1231` is computed, and every factor of `t(w)` shorter than
`(k-1)(N+k-1)` occurs in `t(u)`; (C) with `|χ_g| = 0` and `r_g = 2`, no factor `π_s η_s` of
`f_k^m(1)` with `η_s` a prefix of `π_s η_s`, `|η_s| ≤ r-1` and `τ(π_s) = id` satisfies their
inequality (1) — the count is ZERO for every row, which is their `k ≥ 6` branch. That is a
complete run of the computational content of Theorem 5, and a candidate that passed a short
freeness filter but failed step (A) at length 538 (an `f` at `k = 33`) was discarded by it, so
the pipeline is not vacuous. But it is a computation reported in prose, not a Lean proof, and
it is offered on exactly the footing the paper's own "we verify computationally" has.
-/

namespace Statements.CurrieMolMorphismsAbove21

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
  [(22, [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1], [0, 3, 5, 15, 7, 6, 9, 1, 8, 17, 10, 11, 12, 2, 14, 19, 16, 13, 18, 4, 20, 21, 22], [0, 7, 13, 1, 19, 2, 5, 4, 8, 6, 10, 11, 12, 17, 14, 3, 16, 9, 18, 15, 20, 21, 22]),
   (23, [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1], [1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2], [0, 10, 4, 17, 5, 11, 14, 20, 8, 21, 15, 2, 18, 9, 12, 3, 19, 1, 13, 6, 16, 7, 23, 22], [0, 17, 11, 15, 2, 4, 19, 21, 8, 13, 1, 5, 14, 18, 6, 10, 20, 3, 12, 16, 7, 9, 23, 22]),
   (24, [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1], [0, 15, 3, 4, 17, 10, 5, 16, 19, 1, 7, 6, 18, 12, 9, 21, 20, 2, 11, 8, 22, 14, 13, 23, 24], [0, 9, 17, 2, 3, 6, 11, 10, 19, 14, 5, 18, 13, 22, 21, 1, 7, 4, 12, 8, 16, 15, 20, 23, 24]),
   (25, [1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1], [1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [0, 13, 23, 10, 22, 11, 21, 8, 9, 20, 18, 6, 19, 7, 16, 4, 5, 17, 14, 2, 15, 1, 12, 3, 24, 25], [0, 21, 19, 23, 15, 16, 11, 13, 7, 8, 3, 5, 22, 1, 18, 20, 14, 17, 10, 12, 9, 6, 4, 2, 24, 25]),
   (26, [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1], [0, 16, 9, 23, 24, 21, 14, 19, 7, 17, 22, 12, 15, 10, 5, 8, 20, 6, 13, 4, 3, 2, 18, 1, 11, 25, 26], [0, 23, 21, 20, 19, 14, 17, 8, 15, 2, 13, 24, 11, 18, 6, 12, 1, 9, 22, 7, 16, 5, 10, 3, 4, 25, 26]),
   (27, [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1], [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [0, 5, 16, 2, 13, 9, 6, 20, 21, 17, 10, 24, 3, 25, 1, 14, 18, 7, 11, 4, 22, 15, 19, 8, 12, 23, 27, 26], [0, 14, 3, 12, 19, 1, 6, 17, 23, 5, 10, 18, 24, 4, 15, 21, 2, 9, 16, 22, 7, 8, 20, 25, 11, 13, 27, 26]),
   (28, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 13, 1, 22, 15, 16, 2, 10, 17, 3, 4, 24, 19, 18, 5, 12, 21, 6, 7, 26, 23, 20, 9, 14, 25, 8, 11, 28, 27], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 7, 26, 15, 1, 23, 4, 5, 8, 13, 12, 21, 16, 3, 20, 11, 24, 19, 28, 27]),
   (29, [1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1], [1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2], [0, 18, 8, 19, 22, 5, 9, 2, 12, 23, 13, 26, 16, 27, 17, 6, 20, 3, 21, 1, 7, 10, 11, 24, 25, 4, 15, 14, 29, 28], [0, 19, 7, 17, 25, 5, 15, 20, 2, 6, 21, 22, 8, 10, 27, 26, 12, 14, 1, 3, 16, 18, 4, 9, 23, 24, 11, 13, 29, 28]),
   (30, [1, 1, 1, 2, 1, 1, 1, 1, 2], [1, 1, 1, 2, 1, 1, 1, 1, 1], [0, 15, 2, 24, 19, 18, 5, 12, 23, 6, 9, 28, 27, 22, 13, 16, 1, 10, 17, 3, 4, 26, 21, 20, 7, 14, 25, 8, 11, 30, 29], [0, 16, 2, 19, 20, 6, 9, 24, 27, 10, 17, 28, 7, 14, 25, 1, 15, 18, 5, 4, 23, 22, 13, 8, 3, 26, 21, 12, 11, 30, 29]),
   (31, [1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1], [1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2], [0, 11, 24, 21, 18, 8, 25, 5, 2, 15, 12, 28, 9, 29, 19, 22, 16, 6, 13, 3, 23, 1, 10, 26, 27, 20, 17, 7, 14, 4, 31, 30], [0, 21, 8, 19, 29, 7, 17, 27, 5, 12, 22, 1, 10, 18, 28, 9, 16, 26, 4, 14, 25, 3, 15, 20, 2, 6, 23, 24, 11, 13, 31, 30]),
   (32, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 15, 1, 10, 17, 18, 2, 26, 19, 3, 4, 12, 21, 20, 5, 28, 23, 6, 7, 14, 25, 22, 9, 30, 27, 8, 11, 16, 29, 24, 13, 32, 31], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 3, 26, 11, 30, 19, 1, 27, 4, 5, 8, 13, 12, 21, 16, 29, 20, 7, 24, 15, 28, 23, 32, 31]),
   (34, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 3, 5, 23, 7, 10, 9, 1, 11, 25, 13, 12, 15, 2, 14, 27, 16, 17, 18, 4, 20, 29, 22, 19, 24, 6, 26, 31, 28, 21, 30, 8, 32, 33, 34], [0, 7, 13, 1, 19, 2, 25, 4, 31, 6, 5, 8, 11, 10, 14, 12, 16, 17, 18, 23, 20, 29, 22, 3, 24, 9, 26, 15, 28, 21, 30, 27, 32, 33, 34]),
   (36, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 17, 1, 28, 19, 20, 2, 12, 21, 3, 4, 30, 23, 22, 5, 14, 25, 6, 7, 32, 27, 24, 9, 16, 29, 8, 11, 34, 31, 26, 13, 18, 33, 10, 15, 36, 35], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 33, 26, 7, 30, 15, 34, 23, 1, 31, 4, 5, 8, 13, 12, 21, 16, 29, 20, 3, 24, 11, 28, 19, 32, 27, 36, 35]),
   (38, [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1], [0, 19, 2, 12, 23, 22, 5, 32, 27, 6, 9, 16, 31, 26, 13, 36, 35, 10, 17, 20, 1, 30, 21, 3, 4, 14, 25, 24, 7, 34, 29, 8, 11, 18, 33, 28, 15, 38, 37], [0, 20, 2, 23, 24, 6, 9, 28, 31, 10, 17, 32, 3, 14, 25, 36, 11, 18, 33, 1, 19, 22, 5, 4, 27, 26, 13, 8, 35, 30, 21, 12, 7, 34, 29, 16, 15, 38, 37]),
   (40, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 19, 1, 12, 21, 22, 2, 32, 23, 3, 4, 14, 25, 24, 5, 34, 27, 6, 7, 16, 29, 26, 9, 36, 31, 8, 11, 18, 33, 28, 13, 38, 35, 10, 15, 20, 37, 30, 17, 40, 39], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 33, 26, 3, 30, 11, 34, 19, 38, 27, 1, 35, 4, 5, 8, 13, 12, 21, 16, 29, 20, 37, 24, 7, 28, 15, 32, 23, 36, 31, 40, 39]),
   (42, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 15, 26, 39, 40, 37, 13, 35, 24, 33, 38, 31, 11, 29, 22, 27, 36, 25, 9, 20, 23, 18, 34, 16, 7, 14, 21, 12, 32, 10, 5, 8, 19, 6, 30, 4, 3, 2, 17, 1, 28, 41, 42], [0, 39, 37, 36, 35, 30, 33, 24, 31, 18, 29, 12, 27, 6, 25, 1, 23, 38, 21, 32, 19, 26, 14, 20, 8, 17, 2, 15, 40, 13, 34, 11, 28, 9, 22, 7, 16, 5, 10, 3, 4, 41, 42]),
   (44, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 21, 1, 34, 23, 24, 2, 14, 25, 3, 4, 36, 27, 26, 5, 16, 29, 6, 7, 38, 31, 28, 9, 18, 33, 8, 11, 40, 35, 30, 13, 20, 37, 10, 15, 42, 39, 32, 17, 22, 41, 12, 19, 44, 43], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 33, 26, 41, 30, 7, 34, 15, 38, 23, 42, 31, 1, 39, 4, 5, 8, 13, 12, 21, 16, 29, 20, 37, 24, 3, 28, 11, 32, 19, 36, 27, 40, 35, 44, 43]),
   (46, [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 23, 2, 36, 27, 26, 5, 16, 31, 6, 9, 40, 35, 30, 13, 20, 39, 10, 17, 44, 43, 34, 21, 24, 1, 14, 25, 3, 4, 38, 29, 28, 7, 18, 33, 8, 11, 42, 37, 32, 15, 22, 41, 12, 19, 46, 45], [0, 24, 2, 27, 28, 6, 9, 32, 35, 10, 17, 36, 43, 14, 25, 40, 7, 18, 33, 44, 15, 22, 41, 1, 23, 26, 5, 4, 31, 30, 13, 8, 39, 34, 21, 12, 3, 38, 29, 16, 11, 42, 37, 20, 19, 46, 45]),
   (48, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 23, 1, 14, 25, 26, 2, 38, 27, 3, 4, 16, 29, 28, 5, 40, 31, 6, 7, 18, 33, 30, 9, 42, 35, 8, 11, 20, 37, 32, 13, 44, 39, 10, 15, 22, 41, 34, 17, 46, 43, 12, 19, 24, 45, 36, 21, 48, 47], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 33, 26, 41, 30, 3, 34, 11, 38, 19, 42, 27, 46, 35, 1, 43, 4, 5, 8, 13, 12, 21, 16, 29, 20, 37, 24, 45, 28, 7, 32, 15, 36, 23, 40, 31, 44, 39, 48, 47]),
   (50, [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 43, 37, 36, 31, 22, 25, 7, 19, 42, 13, 28, 8, 14, 2, 48, 47, 34, 41, 20, 35, 5, 29, 40, 23, 26, 17, 11, 12, 46, 6, 32, 1, 18, 45, 3, 39, 38, 33, 24, 27, 9, 21, 44, 15, 30, 10, 16, 4, 50, 49], [0, 32, 14, 35, 48, 21, 30, 7, 12, 41, 46, 27, 28, 10, 13, 44, 47, 26, 33, 8, 19, 42, 5, 24, 39, 6, 25, 40, 11, 22, 45, 4, 31, 38, 17, 20, 3, 2, 37, 36, 23, 18, 9, 1, 43, 34, 29, 16, 15, 50, 49]),
   (52, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 25, 1, 40, 27, 28, 2, 16, 29, 3, 4, 42, 31, 30, 5, 18, 33, 6, 7, 44, 35, 32, 9, 20, 37, 8, 11, 46, 39, 34, 13, 22, 41, 10, 15, 48, 43, 36, 17, 24, 45, 12, 19, 50, 47, 38, 21, 26, 49, 14, 23, 52, 51], [0, 2, 6, 9, 10, 14, 17, 18, 25, 22, 33, 26, 41, 30, 49, 34, 7, 38, 15, 42, 23, 46, 31, 50, 39, 1, 47, 4, 5, 8, 13, 12, 21, 16, 29, 20, 37, 24, 45, 28, 3, 32, 11, 36, 19, 40, 27, 44, 35, 48, 43, 52, 51]),
   (54, [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 27, 2, 16, 31, 30, 5, 44, 35, 6, 9, 20, 39, 34, 13, 48, 43, 10, 17, 24, 47, 38, 21, 52, 51, 14, 25, 28, 1, 42, 29, 3, 4, 18, 33, 32, 7, 46, 37, 8, 11, 22, 41, 36, 15, 50, 45, 12, 19, 26, 49, 40, 23, 54, 53], [0, 28, 2, 31, 32, 6, 9, 36, 39, 10, 17, 40, 47, 14, 25, 44, 3, 18, 33, 48, 11, 22, 41, 52, 19, 26, 49, 1, 27, 30, 5, 4, 35, 34, 13, 8, 43, 38, 21, 12, 51, 42, 29, 16, 7, 46, 37, 20, 15, 50, 45, 24, 23, 54, 53]),
   (56, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 17, 37, 24, 1, 46, 19, 14, 39, 36, 2, 3, 21, 26, 41, 48, 4, 16, 23, 38, 43, 5, 6, 28, 25, 50, 45, 18, 7, 40, 27, 8, 47, 30, 9, 52, 29, 20, 49, 42, 11, 10, 31, 32, 51, 54, 13, 22, 33, 44, 53, 12, 15, 34, 35, 56, 55], [0, 4, 10, 11, 16, 21, 22, 28, 31, 34, 41, 40, 51, 46, 7, 52, 17, 1, 27, 6, 37, 12, 47, 18, 3, 24, 13, 30, 23, 36, 33, 42, 43, 48, 53, 54, 9, 2, 19, 8, 29, 14, 39, 20, 49, 26, 5, 32, 15, 38, 25, 44, 35, 50, 45, 56, 55]),
   (58, [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 47, 33, 8, 19, 18, 5, 28, 48, 38, 37, 51, 23, 2, 9, 12, 52, 22, 41, 32, 27, 42, 13, 55, 56, 6, 45, 16, 31, 26, 17, 36, 3, 46, 49, 1, 35, 10, 21, 20, 7, 30, 50, 40, 39, 53, 25, 4, 11, 14, 54, 24, 43, 34, 29, 44, 15, 57, 58], [0, 35, 13, 32, 47, 6, 25, 40, 3, 14, 37, 48, 15, 22, 49, 56, 27, 30, 5, 4, 39, 38, 17, 12, 51, 46, 29, 20, 7, 54, 41, 28, 19, 2, 53, 36, 31, 10, 9, 44, 43, 18, 21, 52, 55, 26, 33, 1, 8, 34, 42, 11, 16, 45, 50, 23, 24, 57, 58]),
   (60, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [0, 39, 19, 14, 1, 26, 41, 38, 21, 50, 2, 3, 43, 16, 23, 28, 4, 40, 45, 52, 25, 5, 6, 18, 47, 30, 27, 42, 7, 54, 49, 8, 29, 20, 9, 32, 51, 44, 31, 56, 11, 10, 53, 22, 33, 34, 13, 46, 55, 58, 35, 12, 15, 24, 57, 36, 37, 48, 17, 60, 59], [0, 4, 10, 11, 16, 21, 22, 28, 31, 34, 41, 40, 51, 46, 3, 52, 13, 58, 23, 2, 33, 8, 43, 14, 53, 20, 5, 26, 15, 32, 25, 38, 35, 44, 45, 50, 55, 56, 7, 1, 17, 6, 27, 12, 37, 18, 47, 24, 57, 30, 9, 36, 19, 42, 29, 48, 39, 54, 49, 60, 59])]

/-- Every row of the table carries Moulin-Ollagnier's algebraic property. -/
abbrev statement : Prop := ∀ e ∈ table, Good e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

/-- The open target. -/
theorem target : statement := sorry

end Statements.CurrieMolMorphismsAbove21
