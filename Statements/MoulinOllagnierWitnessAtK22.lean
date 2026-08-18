import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# MoulinOllagnierWitnessAtK22 — an explicit `f₂₂` with the algebraic property

Currie–Mol (arXiv:2006.07474v1 = TCS 866 (2021) 51–63) settle `URT(k) = (k−1)/(k−2)` for
`k ∈ {4,…,21}` by exhibiting, for each such `k`, an `r`-uniform binary morphism `f_k` and
then running Moulin-Ollagnier's descent. This problem's own `artifact_schema` names the
algebraic input that descent needs:

> promoting a finite kernel check to the infinite word needs the Moulin-Ollagnier descent,
> which needs the algebraic property `∃ φ ∈ S_k, φ · τ(f(a)) · φ⁻¹ = τ(a)` for `a ∈ {1,2}`,
> where `τ = σ ∘ g`. State which of the two you have.

**This statement is that algebraic property, at `k = 22`, for an explicit morphism, with an
explicit witness `φ`.** `k = 22` is the smallest value Currie–Mol leave open.

## The morphism

`f₂₂(1) = 1111111211112 = 1⁷ 2 1⁴ 2` and `f₂₂(2) = 1111111211111 = 1⁷ 2 1⁵`, both 13-uniform,
with Currie–Mol's fixed `g(1) = 31`, `g(2) = 12`. It was found by an exhaustive sweep of all
`2¹³ × 2¹³` binary morphism pairs of uniformity 13 for the algebraic property, followed by a
freeness filter; the sweep's conventions were fixed by a control that recovers all eighteen
published `f_k`, `k = 4,…,21`, as satisfying the same property under the same code.

`σ`, `act` and `g` are spelled exactly as in `Statements.TauNormalForm`, which pins the
composition convention: `σ(t₁⋯tₙ) = σ(t₁) ∘ ⋯ ∘ σ(tₙ)`, the last letter acting first, so
`τ(1) = σ(31) = σ(3) ∘ σ(1) = ρ`, the step-2 map. Independently value-checked here: with these
definitions `τ(1)` is `(2,4,5,…,22,3,1)` and `τ(2)` is `(2,4,5,…,22,1,3)` on `1,…,22`, matching
`TauNormalForm`'s `ρ` and `ρ ∘ (21,22)`.

## What this does and does not claim

Covers: `φ` is a permutation of `{1,…,22}`; `τ(f₂₂(1))` and `τ(f₂₂(2))` map `{1,…,22)` into
itself; `φ ∘ τ(f₂₂(a)) = τ(a) ∘ φ` for `a ∈ {1,2}` — i.e. `φ · τ(f₂₂(a)) · φ⁻¹ = τ(a)`; and the
two block-side-conditions Theorem 5 also uses (`f₂₂(1)` begins with `1`; the two blocks end in
different letters). Because `f₂₂` is 13-uniform and `22 ≡ 2 (mod 4)`, this is consistent with
`Statements.TauBlockSwapParity`, which forces odd uniformity at such `k`.

Does NOT claim: that `w₂₂` (the word over `Σ₂₂` with prefix `12⋯21` and encoding
`g(f₂₂^ω(1))`) is undirected `(21/20)⁺`-free; that `URT(22) = 21/20`; anything at any other
`k`. The algebraic property is one hypothesis of Currie–Mol's Theorem 5, not its conclusion.
The remaining hypotheses (unique-phase/cut, the `1231` gap bound `N ≤ 30`, and the
kernel-repetition search under their inequality (1), which returns **empty** for this `f₂₂`)
were checked by computer outside Lean and are reported in `message`, not claimed here.
-/

namespace Statements.MoulinOllagnierWitnessAtK22
/-- Currie–Mol's `σ(m)` acting on the letter `j` of `Σ_k = {1,…,k}`: fixes `1,…,m-1`,
sends `j ↦ j+1` for `m ≤ j ≤ k-1`, and sends `k ↦ m`. Identical, character for character,
to `Statements.TauNormalForm.sig`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `σ(t₁ ⋯ tₙ)` applied to `j`. `σ` is a morphism into `S_k` and the product is ordinary
function composition, so `σ(t₁ ⋯ tₙ) = σ(t₁) ∘ ⋯ ∘ σ(tₙ)` and the LAST letter acts first.
This is the convention pinned by Currie–Mol's own worked control `σ(3123131231) = id` over
`Σ₄`, and by `Statements.TauNormalForm`, which fixes `τ(1) = σ(3) ∘ σ(1) = ρ`. -/
def act (k : ℕ) (w : List ℕ) (j : ℕ) : ℕ := w.foldr (sig k) j

/-- `g(1) = 31`, `g(2) = 12`: Currie–Mol's fixed binary-to-ternary morphism for `k ∉ {5,6,8}`. -/
def gblock : ℕ → List ℕ
  | 1 => [3, 1]
  | _ => [1, 2]

/-- `g` extended to a morphism on binary words. -/
def gexp (u : List ℕ) : List ℕ := u.flatMap gblock

/-- `τ(u) = σ(g(u))`, applied to the letter `j`. -/
def tau (k : ℕ) (u : List ℕ) (j : ℕ) : ℕ := act k (gexp u) j

/-- `f₂₂(1) = 1⁷ 2 1⁴ 2`. -/
def F1 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2]

/-- `f₂₂(2) = 1⁷ 2 1⁵`. -/
def F2 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]

/-- The letters `Σ₂₂ = {1,…,22}`. -/
def pts : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

/-- The conjugator `φ ∈ S₂₂`, as a lookup table on `1 ≤ j ≤ 22` (and `0` off-range). -/
def phi (j : ℕ) : ℕ :=
  [0, 1, 2, 16, 4, 9, 6, 3, 8, 18, 10, 11, 12, 5, 13, 20, 15, 14, 17, 7, 19, 22, 21].getD j 0

/-- The canonical proposition. `φ`, `τ(f₂₂(1))` and `τ(f₂₂(2))` all permute the letters
`{1,…,22}`; and on those letters `φ ∘ τ(f₂₂(a)) = τ(a) ∘ φ`, i.e.
`φ · τ(f₂₂(a)) · φ⁻¹ = τ(a)` for `a ∈ {1,2}` — Moulin-Ollagnier's algebraic property.
The first five clauses are the two block side-conditions Currie–Mol's Theorem 5 also uses:
`f₂₂` is 13-uniform, `f₂₂(1)` begins with `1`, and the two blocks end in different letters. -/
abbrev statement : Prop :=
  F1.length = 13 ∧ F2.length = 13 ∧
  F1.head? = some 1 ∧ F1.getLast? = some 2 ∧ F2.getLast? = some 1 ∧
  (pts.map phi).Perm pts ∧
  (pts.map (tau 22 F1)).Perm pts ∧
  (pts.map (tau 22 F2)).Perm pts ∧
  (pts.map (tau 22 F1)).map phi = (pts.map phi).map (tau 22 [1]) ∧
  (pts.map (tau 22 F2)).map phi = (pts.map phi).map (tau 22 [2])

theorem target : statement := sorry

end Statements.MoulinOllagnierWitnessAtK22
