import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocVertexTransitive — the Paley 1-localization is a vertex-transitive graph

Almost everything said about `ϑ(Ḡ_{p,1})` leans on one structural fact and never states it:
`G_{p,1}` is a **vertex-transitive graph**, with the multiplicative group of nonzero squares
of `ZMod p` acting on the vertex set by automorphisms, simply transitively.  That fact is what
licences Lovász's `ϑ(G)ϑ(Ḡ) = n` (Lovász 1979, Theorem 8), what licences symmetrising the
semidefinite program so that it collapses to a Delsarte linear program on a cyclic group, and
what makes "the localization is circulant" true rather than folklore.

This statement is that fact, in five conjuncts, stated on `ZMod p` with `Commons.IsNonzeroSq`
hypotheses so that no `Fintype`/`NeZero` instance juggling intrudes:

1. the nonzero squares are closed under multiplication (the acting group is a group);
2. the action is transitive on them: for nonzero squares `u, v` there is a nonzero square `s`
   with `s * u = v` (and it is unique, `s = v/u`, so the action is simply transitive, the
   vertex set being the group);
3. the action preserves adjacency: `s*u - s*v` is a nonzero square exactly when `u - v` is;
4. adjacency is symmetric — this is where `p ≡ 1 (mod 4)` enters, via `-1` being a square;
5. adjacency is irreflexive, which is automatic since `0` is not a *nonzero* square.

Together, (1)–(3) say `G_{p,1}` is the Cayley graph of the cyclic group of nonzero squares
on the connection set `{t : t and t-1 are both nonzero squares}`, and (4)–(5) say it is a
graph at all.
-/

namespace Statements.PaleyLocVertexTransitive

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 4 = 1 →
    (∀ s t : ZMod p, Commons.IsNonzeroSq s → Commons.IsNonzeroSq t →
        Commons.IsNonzeroSq (s * t)) ∧
    (∀ u v : ZMod p, Commons.IsNonzeroSq u → Commons.IsNonzeroSq v →
        ∃ s : ZMod p, Commons.IsNonzeroSq s ∧ s * u = v) ∧
    (∀ s u v : ZMod p, Commons.IsNonzeroSq s →
        (Commons.IsNonzeroSq (s * u - s * v) ↔ Commons.IsNonzeroSq (u - v))) ∧
    (∀ u v : ZMod p, Commons.IsNonzeroSq (u - v) → Commons.IsNonzeroSq (v - u)) ∧
    (∀ u : ZMod p, ¬ Commons.IsNonzeroSq (u - u))

theorem target : statement := sorry

end Statements.PaleyLocVertexTransitive
