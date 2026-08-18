import Mathlib.GroupTheory.Perm.Sign

/-!
# TauSignBarrier — a parity obstruction on every Currie–Mol morphism, at every `k`

Currie–Mol's Theorem 5 settles `URT(k) = (k-1)/(k-2)` at a given `k` by exhibiting a uniform
binary morphism `f_k` with Moulin-Ollagnier's *algebraic property*

    ∃ φ ∈ S_k,  φ · τ(f(a)) · φ⁻¹ = τ(a)   for a ∈ {1,2},   where τ = σ ∘ g.

This statement is a necessary condition on any such `f`, uniform in `k`, that the paper does
not state and that no search in the literature uses:

> **`|f(1)|₂` must be even and `|f(2)|₂` must be odd.**

## Why

Conjugation preserves sign, so the algebraic property forces `sgn τ(f(a)) = sgn τ(a)`. And
`sgn ∘ τ` is computable letter by letter, because Pansiot's three generators differ from each
other only by small corrections:

* `σ(2) = σ(1) · (1, k)` — a transposition, so `sgn σ(2) = −sgn σ(1)`;
* `σ(3) = σ(1) · (1, k, 2)` — a 3-cycle, so `sgn σ(3) = +sgn σ(1)`.

With `g(1) = 31` and `g(2) = 12` (Currie–Mol's `g_k` for every `k ∉ {5,6,8}`), `τ(1) = σ(3)σ(1)`
and `τ(2) = σ(1)σ(2)`, so `sgn σ(1)` CANCELS in both:

    sgn τ(1) = (sgn σ(1))² = +1,      sgn τ(2) = −(sgn σ(1))² = −1.

The cycle structure of `σ(1)` — the thing that is `k`-dependent and awkward — never enters.
Hence `sgn τ(u) = (−1)^{|u|₂}` for every binary word `u`, and the algebraic property reads
`(−1)^{|f(1)|₂} = +1`, `(−1)^{|f(2)|₂} = −1`.

## What it buys

It cuts the search space for `f_k` by a factor of four at every `k`, uniformly, at no cost —
the test is a parity count on two words. It is also a check that could have failed and did
not: it holds for all eighteen published morphisms `f_4,…,f_21`, and for all twenty-six found
above `k = 21` and filed at `https://jig.so/p/3?s=13` and `?s=16`.

It is an obstruction, not a construction: it rules out three quarters of the candidate
morphisms and says nothing about whether the remaining quarter contains one that works.

## How it is spelled

`Equiv.Perm.sign` needs a `Fintype`, so the permutations live on `Fin k` with the letter `j`
carried by the index `j-1`. The three `σ`'s are produced existentially, and the first three
clauses pin them to Currie–Mol's `σ` letter by letter through `sig`, which is spelled
character for character as in `Statements.TauNormalForm` — so nothing here is a statement
about some other permutation that happens to be convenient. `τ(1) = S₃S₁` and `τ(2) = S₁S₂`
follow the composition convention fixed there: the last letter of a word acts first.
-/

namespace Statements.TauSignBarrier

/-- Currie–Mol's `σ(m)` acting on the letter `j` of `Σ_k = {1,…,k}`: fixes `1,…,m-1`, sends
`j ↦ j+1` for `m ≤ j ≤ k-1`, and sends `k ↦ m`. Identical, character for character, to
`Statements.TauNormalForm.sig` and to `Statements.CurrieMolMorphismsAbove21.sig`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `τ` of a binary word written over the letters `1` and `2`, given the two generator
permutations `T₁ = τ(1)` and `T₂ = τ(2)`:
`τ(c₁c₂⋯c_n) = τ(c₁) · τ(c₂) ⋯ τ(c_n)`, the last letter acting first. -/
def tauOf {k : ℕ} (T1 T2 : Equiv.Perm (Fin k)) (u : List ℕ) : Equiv.Perm (Fin k) :=
  (u.map (fun c => if c = 1 then T1 else T2)).prod

/-- For every `k ≥ 4` there are permutations `S₁, S₂, S₃` of `Fin k` that ARE Currie–Mol's
`σ(1), σ(2), σ(3)` (first three clauses, letter by letter), whose induced `τ(1) = S₃S₁` is
EVEN and `τ(2) = S₁S₂` is ODD, and consequently: any binary words `f(1), f(2)` for which some
`φ` realises Moulin-Ollagnier's algebraic property `φ · τ(f(a)) · φ⁻¹ = τ(a)` must have
`|f(1)|₂` even and `|f(2)|₂` odd. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ S1 S2 S3 : Equiv.Perm (Fin k),
      (∀ i : Fin k, (S1 i).val + 1 = sig k 1 (i.val + 1)) ∧
      (∀ i : Fin k, (S2 i).val + 1 = sig k 2 (i.val + 1)) ∧
      (∀ i : Fin k, (S3 i).val + 1 = sig k 3 (i.val + 1)) ∧
      Equiv.Perm.sign (S3 * S1) = 1 ∧
      Equiv.Perm.sign (S1 * S2) = -1 ∧
      ∀ f1 f2 : List ℕ,
        (∀ c ∈ f1, c = 1 ∨ c = 2) → (∀ c ∈ f2, c = 1 ∨ c = 2) →
        (∃ φ : Equiv.Perm (Fin k),
            φ * tauOf (S3 * S1) (S1 * S2) f1 * φ⁻¹ = S3 * S1 ∧
            φ * tauOf (S3 * S1) (S1 * S2) f2 * φ⁻¹ = S1 * S2) →
        f1.count 2 % 2 = 0 ∧ f2.count 2 % 2 = 1

/-- The open target. -/
theorem target : statement := sorry

end Statements.TauSignBarrier
