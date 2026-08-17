import Mathlib

/-!
# The two orientations of the O'Neill–Verstraëte hypothesis are interchangeable

The source states its hypothesis in two opposite orientations and reconciles them in one
clause.  In the abstract, in Theorem 2, Theorem 3 and **Conjecture 1** the condition is

> `|A_{1,i₁} ∩ ⋯ ∩ A_{k,i_k}|` is **even** if and only if **at least** `t` of the `i_j` are
> distinct,

while **Definition 1**, which is what `b_{k,t}(n)` and the whole covering reduction of
Section 2 are built on, reads

> `|⋂_{j} A_{j,i_j}| = 0 (mod 2) ⟺ |{i₁, …, i_k}| < t`.

These are opposite.  The paper's reconciliation, immediately after Definition 1, is

> "… as one may add an auxiliary element to each set in each family to interchange the parity
> of the sets and their corresponding intersections."

This statement is that clause, made exact: adjoining one fresh ground-set element to every
set of every family is a bijection between the two orientations, at the cost of `m ↦ m + 1`
in the ground set only.  So `b^{Conj 1}_{k,t}` and `b^{Def 1}_{k,t}` agree up to a shift of
the ground set by one, and in particular have the same order of magnitude — which is what
licenses reading Conjecture 1 against the tensor of Definition 2.

Filed because a reader who checks Conjecture 1 against Definition 1 will otherwise find a
contradiction in the source and have no way to tell which line to trust.
-/

namespace Statements.OVParityInterchange

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, inside the ground set `Fin m`. -/
def kInter {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (f : Fin k → Fin N) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter (fun r => ∀ j : Fin k, r ∈ A j (f j))

/-- Conjecture 1's orientation: `|⋂|` is even iff **at least** `t` indices are distinct. -/
def OVHyp (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)) : Prop :=
  ∀ f : Fin k → Fin N, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-- Definition 1's orientation: `|⋂|` is even iff **fewer than** `t` indices are distinct. -/
def IsBollobasTuple (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)) : Prop :=
  ∀ f : Fin k → Fin N, (Even (kInter A f).card ↔ (image f univ).card < t)

/-- Adjoin one fresh ground-set element to every set of every family. -/
def adjoin {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) :
    Fin k → Fin N → Finset (Fin (m + 1)) :=
  fun j i => insert (Fin.last m) ((A j i).image Fin.castSucc)

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  ∀ (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)),
    (OVHyp k t N m A ↔ IsBollobasTuple k t N (m + 1) (adjoin A))

/-- The target. -/
theorem target : statement := sorry

end Statements.OVParityInterchange
