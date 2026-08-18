import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# UPBRemovalSpan224k — which index sets a `(4k+2)`-state UPB in `C²⊗C²⊗C^(4k−1)` must survive

Every construction attempt at `MinUPB224kMinus1` runs into the same question: after the
adversary picks `|a⟩` and `|b⟩`, which states survive, and must their `z`-factors still span
`C^(4k−1)`? This statement answers it once and for all, for **any** family with the
unextendibility property — no orthogonality, no minimality, no construction assumed.

Fix `k ≥ 2`, write `n = 4k+2`, `d = 4k−1 = n−3`, and let `u, w, z` be any families with all
factors nonzero whose product states admit no orthogonal nonzero product state. Then:

1. **any two `z`'s are droppable**: for every `i ≠ j`, the `n−2` vectors `{z_l : l ∉ {i,j}}`
   span `C^d`;
2. **a `u`-parallel pair plus one more is droppable**: if `u_i ∥ u_j` then for every `l`
   the `n−3` vectors `{z_m : m ∉ {i,j,l}}` span `C^d`;
3. the same with the roles of `u` and `w` exchanged.

Each is proved by exhibiting the annihilator explicitly: for `u_i ≠ 0` the vector
`a = (conj (u_i 1), −conj (u_i 0))` is nonzero and satisfies `⟨u_i|a⟩ = 0`, and if
`u_i ∥ u_j` — spelled `u_i 0 · u_j 1 − u_i 1 · u_j 0 = 0` — the same `a` also annihilates
`u_j`. Unextendibility applied to `a ⊗ b ⊗ c` then has nowhere to land unless `c = 0`.

Spanning is spelled in the dual form the callers actually need: *if `c` is orthogonal to
every surviving `z`, then `c = 0`*. That avoids any `Submodule` vocabulary and is exactly
what a proof of unextendibility consumes.

Item 2 is why `MinUPB224kMinus1` is hard: it says the `z`-family must survive the removal of
**three** indices, but only for those triples that are a `u`-parallel class together with one
extra index. It is *not* true for every triple — general position of the `z`'s is impossible
at these parameters — so a construction must place its degeneracies exactly where no such
triple can reach them.

Nothing here is vacuous: at `k = 2` the hypotheses are met by the ten-state witness of
`MinUPB227`, which is already proved.
-/

namespace Statements.UPBRemovalSpan224k

/-- The canonical proposition: the three removal-and-still-spanning facts that any
unextendible family of `4k+2` product states in `C² ⊗ C² ⊗ C^(4k−1)` must satisfy. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∀ u : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ w : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ z : Fin (4 * k + 2) → Fin (4 * k - 1) → ℂ,
      (∀ i, u i ≠ 0) →
      (∀ i, w i ≠ 0) →
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
        ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0) →
      (∀ i j : Fin (4 * k + 2), ∀ c : Fin (4 * k - 1) → ℂ,
          (∀ l, l ≠ i → l ≠ j → (∑ r, star (z l r) * c r) = 0) → c = 0)
    ∧ (∀ i j l : Fin (4 * k + 2),
          u i 0 * u j 1 - u i 1 * u j 0 = 0 →
          ∀ c : Fin (4 * k - 1) → ℂ,
          (∀ m, m ≠ i → m ≠ j → m ≠ l → (∑ r, star (z m r) * c r) = 0) → c = 0)
    ∧ (∀ i j l : Fin (4 * k + 2),
          w i 0 * w j 1 - w i 1 * w j 0 = 0 →
          ∀ c : Fin (4 * k - 1) → ℂ,
          (∀ m, m ≠ i → m ≠ j → m ≠ l → (∑ r, star (z m r) * c r) = 0) → c = 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UPBRemovalSpan224k
