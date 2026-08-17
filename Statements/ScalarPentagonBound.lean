import Mathlib.Data.Nat.Basic

/-!
# ScalarPentagonBound — the scalar step that singles out 5, with its equality case

`(uv + 1)^4 ≤ 5^(u+v)` for all naturals `u, v ≥ 1`, with equality exactly at `u = v = 2`.

This is the pure-arithmetic optimisation the prior campaign calls P4. Read `u` and `v` as the
two block sizes of a product construction: a block pair contributes `uv + 1` to the size and
`u + v` to the card bound, so the inequality says no block splitting beats the pentagon, and
the equality case says the pentagon `(u,v) = (2,2)` — which contributes `5` on `4` — is the
UNIQUE optimum. That is the scalar reason the base in `5^(n/2)` is `5` and not something else.

RELEVANCE, STATED HONESTLY. This is a statement about natural numbers. Its connection to
`m(n,n,1)` runs through the abelian group-invariant branch: Lemma C
(`LemmaCAbelianCosetCover`) bounds `|G|` by `∏ (c_i + 1)`, and this inequality is what turns
such a product bound into a `5^(n/2)` bound. The remaining link — the dictionary between
`1`-cross intersecting set pair systems and coset covers, which the prior campaign calls P5 —
is a HAND proof and is NOT formalized anywhere, here or elsewhere. So this statement does not
connect to the problem root by any machine-checked chain, and must not be cited as if it did.
-/

namespace Statements.ScalarPentagonBound

/-- The canonical proposition: the inequality together with its equality case. -/
abbrev statement : Prop :=
  ∀ u v : ℕ, 1 ≤ u → 1 ≤ v →
    (u * v + 1) ^ 4 ≤ 5 ^ (u + v) ∧
    ((u * v + 1) ^ 4 = 5 ^ (u + v) ↔ u = 2 ∧ v = 2)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.ScalarPentagonBound
