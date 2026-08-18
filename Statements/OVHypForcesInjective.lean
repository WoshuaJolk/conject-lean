import Mathlib

/-!
# The indexed reading of Conjecture 1's hypothesis forces the set-builder reading

O'Neill–Verstraëte write their families as `A_j = {A_{j,i} : 1 ≤ i ≤ m}` — set-builder
notation, so on a strict reading `|A_j| = m` demands the `A_{j,i}` be pairwise distinct for
each fixed `j`.  The root statement of this problem instead uses an indexed family
`A : Fin k → Fin m → Finset (Fin n)` with no injectivity hypothesis, which is the weaker
(easier to satisfy, therefore harder to bound) reading.

This statement shows the two readings coincide wherever the conjecture has content: the
hypothesis itself forces each `A j` to be injective, as soon as `2 ≤ t ≤ k` and `t ≤ m`.

The argument.  Suppose `A j i₁ = A j i₂` with `i₁ ≠ i₂`.  Pick `V` with `i₂ ∈ V`, `i₁ ∉ V` and
`V.card = t - 1`, which `t ≤ m` allows, and build `f` sending the `j`-th coordinate to `i₁` and
the remaining `k - 1 ≥ t - 1` coordinates onto `V`.  Let `g` agree with `f` except `g j = i₂`.
The two intersections are the *same* finset, because the maps differ only in slot `j` and
`A j (f j) = A j (g j)` by assumption.  But `image f univ = insert i₁ V` has `t` elements while
`image g univ = V` has `t - 1`, so the hypothesis calls the one even and the other odd.

Filed because it is the natural objection to the root's formalisation, and it is the kind of
gap no verifier can see: an indexed family that quietly repeats a set is still a perfectly good
inhabitant of the Lean type, and a reader is entitled to ask whether the root has therefore
been weakened away from the paper.  It has not.
-/

namespace Statements.OVHypForcesInjective

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, as a `Finset` of the ground set `Fin n`. -/
def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

/-- The hypothesis of Conjecture 1 at parameter `t`, for `k` families `A_j = {A_{j,i}}`
indexed by `i ∈ [m]` inside the ground set `[n]`: the size of `A_{1,i₁} ∩ ⋯ ∩ A_{k,i_k}` is
even if and only if at least `t` of the indices `i₁, …, i_k` are distinct. -/
def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-- The canonical proposition: under Conjecture 1's hypothesis, with `2 ≤ t ≤ k` and `t ≤ m`,
every family `A j` is injective — so the indexed reading and the paper's set-builder reading
describe the same objects. -/
abbrev statement : Prop :=
  ∀ (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)),
    2 ≤ t → t ≤ k → t ≤ m → OVHyp k t m n A →
      ∀ j : Fin k, Function.Injective (A j)

/-- The target. -/
theorem target : statement := sorry

end Statements.OVHypForcesInjective
