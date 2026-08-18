import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# TwinPrimesDHLReduction — the whole distance from `H₁ ≤ 246` to the conjecture, as one
parameter

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this statement is for

Polymath8b's unconditional record `H₁ ≤ 246` is the composition of two things of completely
different character:

* **`DHL[50,2]`** (Polymath8b Thm 3.2(i)) — analytic, resting on Bombieri–Vinogradov, and
  formalised nowhere: neither Bombieri–Vinogradov, nor GPY, nor Maynard–Tao, nor Zhang
  exists in Mathlib.
* **`H(50) ≤ 246`** — a finite combinatorial certificate: one explicit 50-element set.

This statement formalises **everything except the first bullet**, and pins the residual to
exactly that one named input.  Concretely it proves `DHL[50,2] → H₁ ≤ 246` outright, with
the 50-tuple exhibited and its admissibility checked by the kernel.  Nothing about `H₁` is
asserted unconditionally: the analytic half is a hypothesis, in the open, where it can be
seen.

It also proves `DHL[2,2] →` the twin prime conjecture, in the exact form this problem's root
statement takes.  Put beside the previous line that is the point of the whole exercise:
**the distance between the current world record and the conjecture is the single parameter
`k`, running from 50 down to 2, and nothing else.**  Everything between `DHL[k,2]` and a
statement about `H₁` — the pigeonhole from "two primes in a window" to "two *consecutive*
primes", the passage from frequent small gaps to a `liminf`, the narrow tuple — is
discharged here, once, for all `k` at once.

## Read-back, term by term

* `Admissible H := ∀ p prime, ∃ r < p, ∀ h ∈ H, h % p ≠ r`.  **The bound `r < p` is
  load-bearing.**  Drop it and the clause is vacuously true of every set, since `r := p` is
  never a value of `h % p`.  Two conjuncts check that the predicate discriminates, in both
  directions and by kernel computation: `{0,2}` is admissible, `{0,2,4}` is not (it meets
  every class mod 3).
* `DHL2 k := ∀ H, H.card = k → Admissible H → ∀ N, ∃ n > N, 2 ≤ #{h ∈ H | n + h prime}`.
  This is `DHL[k,2]` verbatim, restricted to shift sets inside `ℕ`; admissibility is
  translation-invariant, so the literature's statement over `ℤ` implies this one, which is
  the direction the hypothesis is used in.  A third conjunct checks `DHL2` is not vacuously
  true: **`¬ DHL2 1`**, because a one-element set cannot contribute two primes.
* `gap` and `H₁` are defined exactly as in `TwinPrimesH1ENat`: `gap n = nth (n+1) − nth n`
  on Mathlib's 0-indexed `Nat.nth Nat.Prime`, and `H₁ = liminf (fun n => (gap n : ℕ∞)) atTop`
  in `ℕ∞`, so no boundedness of the gap sequence is assumed anywhere.
* `tuple50` is an explicit 50-element `Finset ℕ` with `0` and `246` among its elements and
  all elements `≤ 246`, so its diameter is **exactly** 246 and no `ℕ`-subtraction appears.
* The reduction is stated for arbitrary `d` and arbitrary `H`, not just for `50` and `246`,
  so it does not go stale when the record improves: a future `DHL[k,2]` with a narrower
  tuple feeds straight into it.

## The mathematics, in one paragraph

`DHL[k,2]` returns, beyond every bound, an `n` and two distinct shifts `x < y` in `H` with
`n + x` and `n + y` prime.  Those are two primes at distance `y − x ≤ d`, but `H₁` is about
*consecutive* primes, so the gap must be relocated: with `i = count Nat.Prime (n + x)`,
`Nat.nth_count` gives `nth i = n + x`, `count_succ` gives `count (n + x + 1) = i + 1`,
monotonicity of `count` gives `i + 1 ≤ count (n + y)`, and monotonicity of `nth` then gives
`nth (i + 1) ≤ n + y`.  Hence `gap i ≤ d`, with `i` arbitrarily large because `n` was taken
past `nth M`.  Frequently-small gaps give `liminf ≤ d`.  Admissibility of `tuple50` splits at
`p = 50`: primes below it are one kernel `decide` with no `native_decide`, primes above it
are pigeonhole, the image of a 50-element set under `(· % p)` being unable to exhaust
`Finset.range p` once `p > 50`.

## What is not claimed

`DHL[k,2]` is not proved here for any `k`, and neither is any unconditional bound on `H₁`.
The matching lower bound `H(50) ≥ 246` — Engelsma's exhaustive computation, OEIS A008407 —
is not claimed: only that *this* tuple is admissible with diameter 246.  Nothing here bears
on whether the twin prime conjecture is true.
-/

namespace Statements.TwinPrimesDHLReduction

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁`, in `ℕ∞`, so the `sSup` inside `liminf` is the honest supremum. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- A finite set of shifts is *admissible* when for every prime `p` some residue class
`r < p` mod `p` contains no element of it.  The bound `r < p` is load-bearing. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- `DHL[k,2]`: for every admissible `k`-tuple `H` and every bound `N` there is `n > N` such
that at least two of the shifts `n + h`, `h ∈ H`, are prime. -/
def DHL2 (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → Admissible H →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 2 ≤ (H.filter (fun h => Nat.Prime (n + h))).card

/-- An explicit admissible 50-tuple of diameter exactly 246. -/
def tuple50 : Finset ℕ :=
  ([0, 2, 6, 8, 12, 18, 20, 26, 32, 36, 42, 48, 50, 56, 62, 68, 72, 78, 86, 90, 96, 98,
    102, 110, 116, 120, 128, 132, 138, 140, 146, 152, 156, 158, 162, 176, 180, 182, 186,
    188, 198, 200, 210, 212, 216, 218, 230, 240, 242, 246] : List ℕ).toFinset

/-- The canonical proposition: the admissibility predicate discriminates and `DHL2` is not
vacuous; admissibility at primes above the tuple size is automatic; `DHL[k,2]` plus an
admissible `k`-tuple inside `[0, d]` forces `H₁ ≤ d`; `tuple50` is such a tuple for
`k = 50, d = 246`; hence `DHL[50,2] → H₁ ≤ 246`, and `DHL[2,2] → H₁ ≤ 2`, and `DHL[2,2] →`
the twin prime conjecture in the exact form this problem's root statement takes. -/
abbrev statement : Prop :=
  (Admissible ({0, 2} : Finset ℕ) ∧ ¬ Admissible ({0, 2, 4} : Finset ℕ) ∧ ¬ DHL2 1)
  ∧ (∀ (H : Finset ℕ) (p : ℕ), H.card < p → ∃ r < p, ∀ h ∈ H, h % p ≠ r)
  ∧ (∀ (d : ℕ) (H : Finset ℕ), DHL2 H.card → Admissible H → (∀ h ∈ H, h ≤ d) →
      H1 ≤ (d : ℕ∞))
  ∧ (tuple50.card = 50 ∧ 0 ∈ tuple50 ∧ 246 ∈ tuple50 ∧ (∀ h ∈ tuple50, h ≤ 246)
      ∧ Admissible tuple50)
  ∧ (DHL2 50 → H1 ≤ (246 : ℕ∞))
  ∧ (DHL2 2 → H1 ≤ (2 : ℕ∞))
  ∧ (DHL2 2 → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesDHLReduction
