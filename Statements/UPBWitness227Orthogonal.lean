import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# UPBWitness227Orthogonal — the published ten-state witness really is an orthogonal
product set in `C² ⊗ C² ⊗ C^7`

Problem `MinUPB224kMinus1` asks, for every `k ≥ 2`, for `4k+2` nonzero product states in
`C² ⊗ C² ⊗ C^(4k−1)` that are pairwise orthogonal **and** unextendible. At `k = 2` an
explicit integer-entry candidate of size `10` is on record (`jig.so/reports/41`,
independently re-checked in `jig.so/reports/41b`).

This statement machine-checks the FIRST HALF of that candidate's claim, for that exact
witness: all thirty factor vectors are nonzero, and the ten product states are pairwise
orthogonal. It says NOTHING about unextendibility, which is the hard half and remains open
here; so it does not close case `k = 2` of the problem, and the coverage chart does not move
on account of it.

The vectors are pinned by hypothesis rather than inlined three times, which is why the
statement is a `∀` over `u, w, z` with three defining equations. Those hypotheses are
satisfiable by construction — they are equations naming concrete matrices — so nothing here
is vacuous.

Entries are integers, so `star` is inert on them and the same ten states are an orthogonal
product set over `ℝ` and over `ℂ`.
-/

namespace Statements.UPBWitness227Orthogonal

/-- The canonical proposition: for the explicit ten-state candidate in `C² ⊗ C² ⊗ C^7`,
every factor is nonzero and the ten product states are pairwise orthogonal. -/
abbrev statement : Prop :=
  ∀ u : Fin 10 → Fin 2 → ℂ, ∀ w : Fin 10 → Fin 2 → ℂ, ∀ z : Fin 10 → Fin 7 → ℂ,
    u = ![![1, 0],
     ![1, 0],
     ![0, 1],
     ![0, 1],
     ![1, 1],
     ![1, 1],
     ![1, (-1)],
     ![1, (-1)],
     ![1, 2],
     ![2, (-1)]] →
    w = ![![1, 1],
     ![1, 3],
     ![1, 4],
     ![1, 5],
     ![1, 2],
     ![(-4), 1],
     ![(-3), 1],
     ![(-5), 1],
     ![(-1), 1],
     ![(-2), 1]] →
    z = ![![0, 0, (-6), (-5), 1, 1, 0],
     ![1, 0, 0, 0, 0, 0, 0],
     ![5, (-4), (-2), 0, 0, 0, 0],
     ![0, (-3), 6, 1, 1, 0, 0],
     ![0, 0, 0, (-1), 1, (-6), 1],
     ![0, 2, 2, (-3), (-3), 0, 0],
     ![2, 2, 1, (-1), 1, 0, 0],
     ![0, 1, (-2), 3, 3, 0, 0],
     ![0, 0, 0, 0, 0, (-1), (-6)],
     ![0, 0, 0, 0, 0, 0, 1]] →
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UPBWitness227Orthogonal
