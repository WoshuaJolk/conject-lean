import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# UPBDegreeThree224k — in any `(4k+2)`-state UPB in `C²⊗C²⊗C^(4k−1)` every third factor meets
at least three others

The third factors of such a UPB are `n = 4k+2` vectors in `C^d` with `d = n−3`, and almost all
pairs of them are orthogonal — the pair `(i,j)` is allowed to be non-orthogonal only when the
first or the second factor already separates it. This statement bounds that from below: the
non-orthogonality graph of the `z`'s has **minimum degree at least three**, and every edge at
`i` is paid for in the first or the second factor.

Precisely: fix `k ≥ 2` and a family `u, w, z` with all factors nonzero, the `4k+2` product
states pairwise orthogonal, and no nonzero product state orthogonal to all of them. Let `i` be
any index and let `j₁, j₂` be any two indices whose `u`'s are proportional — spelled
`u j₁ 0 · u j₂ 1 − u j₁ 1 · u j₂ 0 = 0`, which at `j₁ = j₂` is vacuous and at `j₁ ≠ j₂` says
they share a `u`-direction. Then there is a `j` outside `{i, j₁, j₂}` with

* `⟨z_i, z_j⟩ ≠ 0`, and
* `⟨u_i, u_j⟩ = 0` or `⟨w_i, w_j⟩ = 0`.

Taking `j₁ = j₂` already gives degree at least two; a genuine `u`-parallel pair gives three.

The proof is four lines and uses only unextendibility. Put `pp v = (conj (v 1), −conj (v 0))`,
which is nonzero and annihilates `v`, and also annihilates every vector proportional to `v`.
If no such `j` existed then `z_i` would be orthogonal to every `z_m` with `m ∉ {i, j₁, j₂}`,
and feeding `a = pp (u j₁)`, `b = pp (w i)` and `c = z_i` to unextendibility leaves the witness
index nowhere to land: at `j₁` and `j₂` the first factor vanishes, at `i` the second, and
everywhere else the third. So `z_i = 0`, which it is not.

**What it is for.** It is the obstruction behind the shape of every solution at these
parameters. In `C²` a parallel class has at most two members, so the `j`'s the statement
produces come from one `u`-class and one `w`-class: each index has `u`-degree at most 2 and
`w`-degree at most 2 in the non-orthogonality graph, with sum at least 3. The same annihilator
argument forces `|P ∪ Q| ≤ 3` for every `u`-class `P` and `w`-class `Q`, so at most two
`w`-classes can have two members; counting then makes `u`-degree 2 compulsory for all but at
most four indices, the two-element `u`-classes must pair into complete bipartite `K₂,₂` blocks
covering all but at most four vertices, and `4 ∤ 4k+2`. Hence **the `z`'s of such a UPB can
never be in general position**: some triple of them must be removable-in-name-only. That is
why the genericity route of Lovász–Saks–Schrijver cannot be repaired here, and why the family
that does work is a cycle of `k` four-state blocks with two leftover states of degree two.

Only the displayed two bullets are claimed in the kernel; the counting in the previous
paragraph is the mathematical companion and is recorded in the version note.

Nothing here is vacuous: the hypotheses are exactly "is a UPB of this size", met at `k = 2` by
`MinUPB227` and at every `k ≥ 3` by `UPBCyclicFamily224k`, both proved, and both have
`u`-classes of size two, so the `u`-parallel hypothesis is met by genuine pairs.
-/

namespace Statements.UPBDegreeThree224k

/-- The canonical proposition: in any unextendible orthogonal product set of `4k+2` nonzero
states in `C² ⊗ C² ⊗ C^(4k−1)`, for every index `i` and every `u`-parallel pair `j₁, j₂` there
is a further index `j` whose third factor is not orthogonal to `z_i`, and which is separated
from `i` in the first or the second factor. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∀ u : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ w : Fin (4 * k + 2) → Fin 2 → ℂ,
    ∀ z : Fin (4 * k + 2) → Fin (4 * k - 1) → ℂ,
      (∀ i, u i ≠ 0) →
      (∀ i, w i ≠ 0) →
      (∀ i, z i ≠ 0) →
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) →
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
        ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0) →
      ∀ i j₁ j₂ : Fin (4 * k + 2),
        u j₁ 0 * u j₂ 1 - u j₁ 1 * u j₂ 0 = 0 →
        ∃ j, j ≠ i ∧ j ≠ j₁ ∧ j ≠ j₂ ∧
          (∑ r, star (z i r) * z j r) ≠ 0 ∧
          ((∑ r, star (u i r) * u j r) = 0 ∨ (∑ r, star (w i r) * w j r) = 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UPBDegreeThree224k
