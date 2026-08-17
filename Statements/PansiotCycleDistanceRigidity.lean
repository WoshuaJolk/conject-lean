import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.ZMod.Basic

/-!
# PansiotCycleDistanceRigidity — the Dejean-import route to Currie–Mol Conjecture 1 is dead

## What this is the invariant of

Currie–Mol (arXiv:2006.07474v1, §4.1) encode an undirected `((k-1)/(k-2))⁺`-free word over
`Σ_k` by a **ternary** Pansiot word, via the morphism `σ : Σ₃* → S_k`

```
σ(1) = (1 2 3 … k)      σ(2) = (2 3 … k) fixing 1      σ(3) = (3 4 … k) fixing 1,2
```

and their constructions all factor through `g : Σ₂* → Σ₃*`, `g(1) = 31`, `g(2) = 12` (their
fixed choice for every `k ∉ {5,6,8}`), giving `τ = σ ∘ g`. Recomputed from the paper's own `σ`
in this session (exact integer permutations, composition convention pinned by their control
`σ(3123131231) = id` over `Σ₄`), for every `k` in `4 … 61`:

```
τ(1) = ρ  where  ρ : 1 ↦ 2,  j ↦ j+2 (2 ≤ j ≤ k-2),  k-1 ↦ 3,  k ↦ 1
τ(2) = ρ ∘ (k-1, k)
```

and `ρ` is a `k`-cycle exactly when `k` is odd, with `k-1` and `k` at **cyclic distance
`(k-1)/2`** inside it. The *binary* Pansiot pair that the whole large-alphabet Dejean machinery
(Pansiot; Carpi 2007; Currie–Rampersad, arXiv:0901.3188) is built on is `(σ(1), σ(2))`, and
`σ(1)⁻¹σ(2) = (1, k)`, at cyclic distance **1** inside the `k`-cycle `σ(1)`.

So both pairs have the shape (`k`-cycle `γ`, `γ` composed with a transposition of two points of
`γ` at cyclic distance `m`). Relabelling the `k`-cycle to `x ↦ x + 1` on `ZMod k` and
translating, the pair becomes `(c, c ∘ swap 0 m)`. **This statement is the assertion that `m`
is a complete invariant of such a pair up to simultaneous conjugacy, up to sign.**

## Why that kills the route

`(k-1)/2 ≢ ±1 (mod k)` for every odd `k ≥ 5`. So `(τ(1), τ(2))` is not simultaneously conjugate
to the binary Pansiot pair; since `⟨τ(1), τ(2)⟩ = S_k` and every automorphism of `S_k` is inner
for `k ≠ 6`, `ker τ ≠ ker(binary Pansiot morphism)`. Dejean-optimality of an encoding is a
condition on the *binary* kernel, so it does not control the undirected kernel, and a
Dejean-optimal binary word fed through `g` carries no guarantee. That is not hypothetical: an
explicit `τ`-kernel repetition appears at `k = 27, 29, 31` (Jig report 56 — the period word `π`
has `|π| = 280` at `k = 27`, with `τ(π) = id` and `φ(π) ≠ id`).

Independently checked here: `τ(1) = ρ` and `τ(2) = ρ∘(k-1,k)` for all `k` in `4…61`; `ρ` a
`k`-cycle for odd `k` and of type `(k/2+1, k/2-1)` for even `k`, same range; distance `(k-1)/2`,
same range; and **brute force over all of `S_k` at `k = 5, 7, 9` finds no simultaneous
conjugator**, which is the statement below instantiated at `m = (k-1)/2`.

## The statement

For `k ≥ 3`, with `c = (x ↦ x + 1)` on `ZMod k`: a permutation simultaneously fixing `c` under
conjugation and carrying `swap 0 m` to `swap 0 1` exists **iff** `m = 1` or `m = -1`.

Elementary content: the centraliser of the `k`-cycle `c` in `Sym (ZMod k)` is the group of
translations, and a translation by `j` sends `swap 0 m` to `swap j (m+j)`; `{j, m+j} = {0,1}`
forces `m = ±1`. The `k ≥ 3` hypothesis rules out the degenerate case `swap 0 1 = 1`.
-/

namespace Statements.PansiotCycleDistanceRigidity

/-- The standard `k`-cycle on `ZMod k`, `x ↦ x + 1`. -/
def c (k : ℕ) : Equiv.Perm (ZMod k) := Equiv.addRight (1 : ZMod k)

/-- The canonical proposition: cyclic distance is a complete invariant, up to sign, of a pair
(`k`-cycle, `k`-cycle composed with a transposition) up to simultaneous conjugacy. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ m : ZMod k,
    (∃ ψ : Equiv.Perm (ZMod k),
        ψ * c k * ψ⁻¹ = c k ∧ ψ * Equiv.swap 0 m * ψ⁻¹ = Equiv.swap 0 1)
      ↔ (m = 1 ∨ m = -1)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.PansiotCycleDistanceRigidity
