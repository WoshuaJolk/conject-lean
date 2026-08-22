import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Sum

/-!
# CopiesTransversalCore — the deterministic core of the copies lemma

Convention (as in `SpanningOrthRep4C10` and `SpanningOrthRep4Copies20`, the opposite of
Lovász–Saks–Schrijver): an edge of the orthogonality graph means the two vectors *are* orthogonal.

Background. At the target size `f_N + 1` the degree budget forces one factor of the witness to be
*degenerate*: a `k`-regular orthogonality graph in dimension `k` whose vectors are still
`(k+1)`-spanning, i.e. no `k + 1` of them lie in a common hyperplane. Chen–Johnston build such a
representation in every dimension but only on at most `2k` vertices, and that ceiling is exactly
their dominance hypothesis, so the reach of their theorem is the reach of the gadget.

The route past the ceiling is to place several gadgets in generic relative position. That argument
splits cleanly into two halves:

* a *genericity* half, saying that for generic unitaries the resulting configuration is
  transversal — the span of a piece of block one and a piece of block two has the largest
  dimension the two pieces allow. That half is about Zariski density and is not what this
  statement is about.
* a *deterministic* half, isolated here: transversality plus the two blocks' own tightness and
  `(k+1)`-spanning already forces the union to be tight and `(k+1)`-spanning, with no genericity
  and no reference to how the blocks were produced.

The deterministic half is where the mathematical content of the copies argument lives: a subset of
size `k + 1` either sits inside a single block, where that block's spanning property applies, or is
split, and then the two pieces contribute at least `k` dimensions between them — because a piece of
size at most `k - 1` is independent by tightness, and a piece of size `k` still has rank at least
`k - 1`, leaving the single leftover vector to supply the last dimension. So two dependent pieces
can never conspire inside `k + 1` vectors.

Stated for two blocks; iterating it gives unions of arbitrarily many blocks, which is what makes
achievable gadget sizes closed under addition. Blocks are *not* required to be copies of one
another, so the two sizes may differ.

No claim is made here about the genericity half, about which unitaries are transversal, or about
the existence of any particular seed.
-/

namespace Statements.CopiesTransversalCore

variable {k : ℕ}

/-- The Hermitian pairing on `Fin k → ℂ`, conjugate-linear in the first slot. -/
abbrev pair (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The rank of the subfamily of `v` indexed by a finite set `S`: the dimension of its span. -/
noncomputable abbrev rk {ι : Type} (v : ι → Fin k → ℂ) (S : Finset ι) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i))

/-- Tight: every at most `k - 1` of the vectors are linearly independent. This is the hypothesis
that makes a gadget reusable — it is what survives being copied. -/
abbrev Tight {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card ≤ k - 1 → LinearIndependent ℂ fun i : (S : Set ι) => v i

/-- `(k+1)`-spanning: no `k + 1` of the vectors lie in a common hyperplane. Equivalently, no
nonzero vector is orthogonal to more than `k` of them, which is the killing-number bound the
unextendability count consumes. -/
abbrev Spanning {ι : Type} [Fintype ι] (v : ι → Fin k → ℂ) : Prop :=
  ∀ S : Finset ι, S.card = k + 1 →
    Submodule.span ℂ (Set.range fun i : (S : Set ι) => v i) = ⊤

/-- Transversality of the two blocks: the span of a piece of each block is as large as the two
pieces' own ranks permit. This is the conclusion of the genericity half of the copies argument,
taken here as a hypothesis. -/
abbrev Transversal {n₁ n₂ : ℕ} (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ) : Prop :=
  ∀ (S : Finset (Fin n₁)) (T : Finset (Fin n₂)),
    rk (Sum.elim u w) (S.disjSum T) = min k (rk u S + rk w T)

/-- The canonical proposition.

Fix a dimension `k ≥ 2` and two families `u`, `w` of vectors in `C^k`, each tight and
`(k+1)`-spanning, no vector of one orthogonal to any vector of the other, and transversal in the
sense above. Then the union is again tight and `(k+1)`-spanning, and every orthogonal pair in the
union lies inside a single block — so the orthogonality graph is the disjoint union of the two
blocks' graphs, and the union is a gadget of the combined size, reusable in turn. -/
abbrev statement : Prop :=
  ∀ (k n₁ n₂ : ℕ), 2 ≤ k →
    ∀ (u : Fin n₁ → Fin k → ℂ) (w : Fin n₂ → Fin k → ℂ),
      Tight u → Spanning u → Tight w → Spanning w →
      (∀ (i : Fin n₁) (j : Fin n₂), pair (u i) (w j) ≠ 0) →
      Transversal u w →
      Tight (Sum.elim u w) ∧ Spanning (Sum.elim u w) ∧
        (∀ a b : Fin n₁ ⊕ Fin n₂,
          pair (Sum.elim u w a) (Sum.elim u w b) = 0 →
            (∃ i j, a = Sum.inl i ∧ b = Sum.inl j) ∨ (∃ i j, a = Sum.inr i ∧ b = Sum.inr j))

theorem target : statement := sorry

end Statements.CopiesTransversalCore
