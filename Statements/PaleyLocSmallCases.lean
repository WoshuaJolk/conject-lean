import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

namespace Statements.PaleyLocSmallCases

/-- The canonical proposition: the small-case data of the Paley 1-localization.

For `p = 13` and `p = 17` the 1-localization of the Paley graph — the graph on the nonzero
squares of `ZMod p`, with `u` joined to `v` when `u - v` is a nonzero square — has exactly
`(p-1)/2` vertices and exactly `(p-1)/2 * (p-5)/4` ordered adjacent pairs, and the adjacency
relation is symmetric and irreflexive.  Everything is decidable; nothing is asymptotic. -/
abbrev statement : Prop :=
  Fintype.card {x : ZMod 13 // x ≠ 0 ∧ ∃ r : ZMod 13, x = r * r} = 6 ∧
  Fintype.card {x : ZMod 17 // x ≠ 0 ∧ ∃ r : ZMod 17, x = r * r} = 8 ∧
  (Finset.univ.filter (fun q : {x : ZMod 13 // x ≠ 0 ∧ ∃ r : ZMod 13, x = r * r} ×
      {x : ZMod 13 // x ≠ 0 ∧ ∃ r : ZMod 13, x = r * r} =>
      ((q.1 : ZMod 13) - (q.2 : ZMod 13)) ≠ 0 ∧
        ∃ r : ZMod 13, ((q.1 : ZMod 13) - (q.2 : ZMod 13)) = r * r)).card = 12 ∧
  (Finset.univ.filter (fun q : {x : ZMod 17 // x ≠ 0 ∧ ∃ r : ZMod 17, x = r * r} ×
      {x : ZMod 17 // x ≠ 0 ∧ ∃ r : ZMod 17, x = r * r} =>
      ((q.1 : ZMod 17) - (q.2 : ZMod 17)) ≠ 0 ∧
        ∃ r : ZMod 17, ((q.1 : ZMod 17) - (q.2 : ZMod 17)) = r * r)).card = 24 ∧
  (∀ u v : {x : ZMod 13 // x ≠ 0 ∧ ∃ r : ZMod 13, x = r * r},
      (((u : ZMod 13) - v) ≠ 0 ∧ ∃ r : ZMod 13, ((u : ZMod 13) - v) = r * r) →
      (((v : ZMod 13) - u) ≠ 0 ∧ ∃ r : ZMod 13, ((v : ZMod 13) - u) = r * r)) ∧
  (∀ u : {x : ZMod 17 // x ≠ 0 ∧ ∃ r : ZMod 17, x = r * r},
      ¬ (((u : ZMod 17) - u) ≠ 0 ∧ ∃ r : ZMod 17, ((u : ZMod 17) - u) = r * r))

theorem target : statement := sorry

end Statements.PaleyLocSmallCases
