import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# FranklUnionClosed — the union-closed sets conjecture

This module is the **single source of truth** for what this problem means.  The verifier
reads `Statements.FranklUnionClosed.statement` and nothing else.  It is deliberately
self-contained: it imports only `Mathlib` and uses no `Commons` module.

## The informal statement, and the term-by-term read-back

Frankl's union-closed sets conjecture (1979): in any finite nonempty family of finite sets
closed under union, if the union of all members is nonempty, then some element of the ground
set belongs to at least half the sets in the family.

Read back against the Lean below, term by term:

* "any finite family of sets" → `∀ (α : Type) [DecidableEq α] (F : Finset (Finset α))`.
  The family `F` is finite by construction (it is a `Finset`), and each member is a finite
  set (a `Finset α`).  The type `α` is arbitrary subject to decidable equality.
* "nonempty" → `F.Nonempty`.  The family contains at least one set.
* "closed under union" → `∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F`.  The union of any two members is
  also a member.
* "the union of all members is nonempty" → `∃ A ∈ F, A.Nonempty`.  This is equivalent to
  `⋃₀ F ≠ ∅`: if some member `A` is nonempty then certainly the union is, and conversely
  any element of the union lies in some member.
* "some element of the ground set" → `∃ x : α, …`.  The element is drawn from `α`, the
  ambient type.
* "belongs to at least half the sets" → `(F.filter (fun A => x ∈ A)).card * 2 ≥ F.card`.
  The count of sets containing `x`, doubled, is at least the family size.  This is the
  standard integer encoding of `count ≥ |F| / 2` and is exact for both even and odd `|F|`.

## Non-vacuity

The hypotheses are jointly satisfiable: `F = {∅, {0}}` over `α = ℕ` is union-closed,
nonempty, and has a nonempty member.  The conclusion holds: element `0` is in `1` of `2`
sets, and `1 * 2 = 2 ≥ 2`.

The conjecture is open: no proof is known that this holds for *every* such family, and no
counterexample has been found.

## The number the progress space tracks

Write `c` for the supremum of constants such that every nonempty finite union-closed family
with nonempty union has an element in at least a `c`-fraction of its sets.  The conjecture
asserts `c = 1/2`.

The current bounds, all proof-grade:
* **Lower:** `(3 - √5) / 2 ≈ 0.38197`, proved by Alweiss–Huang–Sellke (arXiv:2211.11731,
  published Elec. J. Combin. 31(3) #P3.35, 2024, DOI 10.37236/12232), building on the
  information-theoretic method of Gilmer (arXiv:2211.09055).  The constant `(3 - √5) / 2`
  is the limit of the i.i.d.-coupling method.
* **Upper:** `1/2`, tight: the family `{∅, {1}}` has `|F| = 2` and its most frequent
  element appears in exactly `1` set.
* Preprint improvements to `~0.3827` (Liu, arXiv:2306.08824; Cambie, arXiv:2212.12500)
  go slightly beyond the i.i.d. ceiling using non-i.i.d. couplings but are not
  peer-reviewed.

The squeeze is `(3 - √5) / 2 ≤ c ≤ 1/2`, and the conjecture says `c = 1/2`.
-/

namespace Statements.FranklUnionClosed

/-- The canonical proposition.  This is the type the verifier demands.

For every type `α` with decidable equality, every nonempty finset `F` of finsets of `α`
that is closed under union and has at least one nonempty member: there exists an `x : α`
such that the number of members of `F` containing `x`, doubled, is at least `|F|`. -/
abbrev statement : Prop :=
  ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
    F.Nonempty →
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    (∃ A ∈ F, A.Nonempty) →
    ∃ x : α, (F.filter (fun A => x ∈ A)).card * 2 ≥ F.card

/-- The open target.  Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.FranklUnionClosed
