import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# GenPosUPBTrivialCeiling — general position stops at the trivial bound, in every system

Every known minimum-size unextendible product basis is built by the orthogonal-representation
method of Alon & Lovász (*Unextendible product bases*, JCTA **95** (2001) 169–179, Thm 3.1),
which realises an edge-colouring of `K_m` by local families in **general position**: any `dⱼ`
of the `j`-th local vectors are linearly independent. General position is what makes such a
construction work at all, because it makes unextendibility automatic — a nonzero local vector
can annihilate at most `dⱼ − 1` members of a general-position family, so no distribution of the
states among the parties can leave a factor unspanned.

This statement says that method has a ceiling, and that the ceiling is exactly the trivial
lower bound `f_N(d₁,…,d_p) = 1 + Σⱼ(dⱼ − 1)`, in every multipartite system at once.

The mechanism is a degree count, and it needs only pairwise orthogonality — unextendibility is
not among the hypotheses, so the ceiling applies to every general-position pairwise-orthogonal
family, UPB or not. Fix one state `i₀`. Every other state is orthogonal to it in at least one
factor, so the other `m − 1` states are covered by the sets
`Aⱼ = {i ≠ i₀ : ⟨vᵢ₀ⱼ | vᵢⱼ⟩ = 0}`. General position caps `|Aⱼ| ≤ dⱼ − 1`: the members of `Aⱼ`
lie in the kernel of the linear functional `y ↦ ⟨vᵢ₀ⱼ | y⟩`, and `dⱼ` of them would be
linearly independent, hence a basis of `C^{dⱼ}`, forcing that functional to vanish identically
and so `⟨vᵢ₀ⱼ|vᵢ₀ⱼ⟩ = 0`, i.e. `vᵢ₀ⱼ = 0`, contrary to hypothesis. Summing,
`m − 1 ≤ Σⱼ(dⱼ − 1)`.

## Consequence, and why it is filed here

Whenever the minimum UPB size exceeds the trivial bound — which by Alon–Lovász Cor. 4.1(i) is
the case for every system with `f_N` odd and some `dⱼ` even — a minimum-size UPB **cannot**
have all its local families in general position. It must be locally degenerate, and by the same
count degenerate in exactly one unit: one factor must carry a dependent `dⱼ`-subset, and one is
enough. This is the method ceiling for the root question `MinUPBAtMostTrivialPlusOne`, and it is
what makes that question a design problem (which degree sequences are realisable) rather than a
search.

The fixed-dimension instance at `(3,4,4)` is `GenPosUPB344Dead` on `jig.so/p/13`; the two
witnesses on the board, `MinUPB344` (`(3,4,4)`, ten states) and `MinUPB224kMinus1`
(`(2,2,4k−1)`, `4k+2` states), both sit one above their trivial bound and both are locally
degenerate in exactly the manner this count forces.

The bound is sharp and is not an obstruction to `f_N` itself: general-position families of size
`f_N` exist (Alon–Lovász Thm 3.1 realises them whenever the corresponding edge-colouring
exists), so this statement bites only at `f_N + 1`.

## Reading the formalisation

Local vectors are indexed as `v i j : Fin (d j) → ℂ`, the `j`-th factor of the `i`-th product
state; no tensor product is formed. The inner product is the standard Hermitian one,
conjugate-linear in the first slot, and a product state pairing `∏ⱼ ⟨vᵢⱼ|vᵢ'ⱼ⟩` vanishes iff
some factor pairing does, which is the `∃ j` in the orthogonality hypothesis.

`GenPos v j` is general position in factor `j`: any injectively-indexed `dⱼ` of the `j`-th
local vectors are linearly independent. When `m < dⱼ` there is no such indexing and the
condition is vacuous, which is harmless — the count then bounds `|Aⱼ|` by `m − 1 < dⱼ` anyway.
-/

namespace Statements.GenPosUPBTrivialCeiling

/-- General position in factor `j`: any `d j` of the `j`-th local vectors, taken at distinct
indices, are linearly independent. -/
abbrev GenPos {p m : ℕ} {d : Fin p → ℕ} (v : Fin m → (j : Fin p) → Fin (d j) → ℂ)
    (j : Fin p) : Prop :=
  ∀ f : Fin (d j) → Fin m, Function.Injective f →
    LinearIndependent ℂ (fun t : Fin (d j) => v (f t) j)

/-- The canonical proposition.

A family of `m` product states in `C^{d₁} ⊗ ⋯ ⊗ C^{d_p}` with all factors nonzero, pairwise
orthogonal, and with every local family in general position, satisfies
`m ≤ f_N(d₁,…,d_p) = 1 + Σⱼ(dⱼ − 1)`. Unextendibility is not assumed. -/
abbrev statement : Prop :=
  ∀ p m : ℕ, ∀ d : Fin p → ℕ, ∀ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
    (∀ i j, v i j ≠ 0) →
    (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) →
    (∀ j, GenPos v j) →
    m ≤ 1 + ∑ j, (d j - 1)

/-- The target. -/
theorem target : statement := sorry

end Statements.GenPosUPBTrivialCeiling
