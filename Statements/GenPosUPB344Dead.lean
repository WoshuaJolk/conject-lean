import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fin.VecNotation

/-!
# GenPosUPB344Dead — the general-position route to `MinUPB344` is dead

Every known minimum-size UPB is built by the orthogonal-representation method of
Alon–Lovász (*Unextendible product bases*, JCTA **95** (2001) 169–179, Thm 3.1),
which uses Lovász–Saks–Schrijver to realise an edge-colouring of `Kₙ` by local
families in **general position**: every `dⱼ` of the `j`-th factors linearly
independent. General position is what makes unextendibility automatic — a nonzero
`a` can kill at most `dⱼ − 1` of the `j`-th factors, so no partition of the states
into three parts can fail to span everywhere.

This statement says that route cannot reach cardinality ten in `C³ ⊗ C⁴ ⊗ C⁴`, and it
says it for pairwise orthogonality alone — unextendibility is not assumed, so the
obstruction applies to every general-position candidate, UPB or not.

The mechanism is a degree count. Fix one state. Each of the other nine is orthogonal
to it on some factor, so the nine are covered by the three sets
`Aⱼ = {i : ⟨vⱼ|vⱼ(i)⟩ = 0}`. General position caps `|Aⱼ| ≤ dⱼ − 1`: the members of
`Aⱼ` lie in the hyperplane orthogonal to the fixed state's `j`-th factor, so `dⱼ` of
them would be linearly independent vectors spanning `C^{dⱼ}` and all orthogonal to a
nonzero vector. Hence `9 ≤ (3−1) + (4−1) + (4−1) = 8`, which is false.

The same count is the reason the trivial lower bound `f_N(d₁,…,d_p) = 1 + Σ(dⱼ − 1)`
is where general position stops: it bounds a general-position pairwise-orthogonal
family by `1 + Σ(dⱼ − 1) = 9` states here. So at ten the local families must be
degenerate, which is the residual `UPB344Degenerate`.

Note the count does **not** rule out ten states as such (ten pairwise-orthogonal
product states exist, e.g. ten distinct computational-basis products), nor does it
bite at nine, where the capacity `8` exactly matches the requirement; at nine the
obstruction is instead the Alon–Lovász parity argument, which is out of scope here.
-/

namespace Statements.GenPosUPB344Dead

/-- General position in the `3`-dimensional factor: any three distinct indices carry
linearly independent local vectors. -/
abbrev GenPos3 (u : Fin 10 → Fin 3 → ℂ) : Prop :=
  ∀ i j k : Fin 10, i ≠ j → i ≠ k → j ≠ k → LinearIndependent ℂ ![u i, u j, u k]

/-- General position in a `4`-dimensional factor: any four distinct indices carry
linearly independent local vectors. -/
abbrev GenPos4 (x : Fin 10 → Fin 4 → ℂ) : Prop :=
  ∀ i j k l : Fin 10, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    LinearIndependent ℂ ![x i, x j, x k, x l]

/-- The canonical proposition.

There is no family of `10` nonzero product states in `C³ ⊗ C⁴ ⊗ C⁴` that is pairwise
orthogonal and has all three local families in general position. Unextendibility is
not among the hypotheses, so this kills the general-position route to `MinUPB344`
outright. -/
abbrev statement : Prop :=
  ¬ ∃ u : Fin 10 → Fin 3 → ℂ,
    ∃ w : Fin 10 → Fin 4 → ℂ,
    ∃ z : Fin 10 → Fin 4 → ℂ,
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
      GenPos3 u ∧ GenPos4 w ∧ GenPos4 z

/-- The target. -/
theorem target : statement := sorry

end Statements.GenPosUPB344Dead
