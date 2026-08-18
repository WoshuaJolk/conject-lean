import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# An explicit `f₂₂` and `φ` with Moulin-Ollagnier's algebraic property at `k = 22`

Every clause is a finite computation over `{1,…,22}`, discharged by `decide`; the kernel
evaluates `σ` on 22 letters through the 26-letter word `g(f₂₂(a))`.

Forced-answer controls run against the same definitions before submitting (they are not part
of the claim, so they are not shipped in this file): `τ(1)` and `τ(2)` evaluate to
`(2,4,5,…,22,3,1)` and `(2,4,5,…,22,1,3)`, matching `TauNormalForm`'s `ρ` and `ρ ∘ (21,22)`;
and three must-fail probes are provable as **negations** — the identity permutation does not
conjugate `τ(f₂₂(1))` to `τ(1)`; a `φ` with its last two entries transposed does not either;
and `φ` does not conjugate `τ(f₂₂(2))` to `τ(1)`. So the conjugation clauses are not vacuous
and are not satisfied by an arbitrary map.
-/

namespace Submissions.MoulinOllagnierWitnessAtK22.OpusFamilySweep
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

theorem proof : statement :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide⟩

end Submissions.MoulinOllagnierWitnessAtK22.OpusFamilySweep
