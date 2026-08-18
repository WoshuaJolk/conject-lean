import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# TwinPrimesH1Attained — `H₁`, when finite, is attained, is even, and is a de Polignac gap

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The gap this fills

Problem 9's progress unit reads: "`H₁` is even, so only the `123` even values from `2` to
`246` remain live."  Nothing on the board proves that sentence.  `TwinPrimesGapParity`
proves the arithmetic — every gap past the first is even and `≥ 2` — and says explicitly
that the step from "the *sequence* is eventually even" to "`H₁` is even" is **not**
formalised.  `TwinPrimesH1ENat` defines `H₁` honestly in `ℕ∞` and proves `2 ≤ H₁`, but says
nothing about its parity.  The step between them is the content here, and it is not
automatic: a liminf need not be a value of the sequence in general.  In `ℕ∞` along `atTop`
it is, whenever it is finite, and that is what makes parity transfer.

## What is claimed

**(0) The general fact, for an arbitrary `ℕ∞`-valued sequence.**  If
`liminf u atTop = (m : ℕ∞)` with `m` a *natural number*, then `m ≤ u n` eventually and
`u n = m` frequently.  Nothing about primes enters; this is the lattice fact that everything
below is an application of.  The finiteness of `m` is load-bearing — `u n = n` has liminf `⊤`
and takes the value `⊤` never — which is why the conclusion is stated for `m : ℕ` and not for
an arbitrary element of `ℕ∞`.

**(1) `H₁` is attained infinitely often, when it is finite.**  If `H₁ = m` for a natural
number `m`, the set of indices `n` with `gap n = m` is infinite.

**(2) `H₁` is even and at least `2`, when it is finite.**  This is the sentence in the
problem's progress unit, now a checked fact rather than prose.  It follows from (1): the
value is attained at some index `≥ 1`, and every gap from index `1` on is even and positive.

**(3) `H₁` is a de Polignac gap, when it is finite.**  If `H₁ = m` then for every bound `N`
there is a prime `p > N` with `p + m` prime.  This is the conjunction that gives the problem
its shape: the twin prime conjecture is the case `m = 2`, and the *only* thing standing
between the recorded ceiling and a de Polignac theorem is which even `m` the liminf is.

**(4) The packaged corollary.**  Any finite ceiling on `H₁` yields such an `m`: if
`H₁ ≤ B` then there is an even `m` with `2 ≤ m ≤ B`, attained infinitely often, and with
infinitely many prime pairs `(p, p + m)`.  Instantiating `B = 246` — Polymath8b Theorem
1.4(i), which is *not* formalised here or anywhere and is **not** assumed by this statement —
is exactly the assertion that some even `m ≤ 246` is a de Polignac gap, and that the live
values are the `123` even numbers from `2` to `246`.

**(5) A forced-answer control.**  On `u n = 3` for even `n` and `5` for odd `n`, the `liminf`
is `3` and the `limsup` is `5`.  This is here because conjuncts (1)–(4) are all conditional
on `H₁` being finite, which nobody can currently establish, so a reader is entitled to ask
whether the theorem has any content at all.  The control answers two distinct doubts at once:
it exhibits a sequence whose liminf *is* a finite natural number, so the hypothesis of (0) is
satisfiable and (0) is not vacuous; and it pins down that `Filter.liminf` on this codomain
computes the smaller value attained infinitely often and not the larger.  Had the intended
reading been wrong — had this been a `limsup`, or the `ℕ`-valued junk convention — the
conjunct would read `5 = 3` or `0 = 3` and would be unprovable.

## What is NOT claimed

`H₁ < ⊤` is **not** claimed, assumed, or used.  That is Zhang's theorem, sharpened by
Polymath8b, and it is formalised nowhere.  Every conjunct above is either unconditional (0, 5)
or explicitly hypothetical in the finiteness of `H₁` (1–4).  No upper bound on `H₁` is proved;
no sieve, no Bombieri–Vinogradov, no exponent of distribution appears.  The twin prime
conjecture is neither proved nor made easier: (3) at `m = 2` is the conjecture, and this
statement does not decide `m`.

## Read-back, term by term

* `gap n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n`, on Mathlib's 0-indexed
  enumeration, truncated natural subtraction, exactly as in `TwinPrimesH1ENat`.
* `H1 = liminf (fun n => (gap n : ℕ∞)) atTop`, cast into `ℕ∞`, exactly as in
  `TwinPrimesH1ENat`.  The `ℕ∞` codomain is what makes `H₁` faithful without assuming
  boundedness; see that statement for the argument.
* `H1 = (m : ℕ∞)` with `m : ℕ` is how "`H₁` is finite and equals `m`" is said.
* `{n | gap n = m}.Infinite` is Mathlib's `Set.Infinite`.
* "there are infinitely many primes `p` with `p + m` prime" is written in the same unbounded
  `∀ N, ∃ p, N < p ∧ …` form the root statement of this problem uses, so that conjunct (3)
  at `m = 2` is literally the root.
-/

namespace Statements.TwinPrimesH1Attained

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`: `gap 0 = 3 - 2 = 1`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁`, the least gap between consecutive primes attained infinitely often, as an element
of `ℕ∞`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The canonical proposition.  A finite `liminf` of an `ℕ∞`-valued sequence is attained
frequently; hence `H₁`, if finite, is attained infinitely often, is even and at least `2`,
and is a de Polignac gap; hence any finite ceiling `B` on `H₁` produces an even
`m ∈ [2, B]` with infinitely many prime pairs `(p, p + m)`.  The last conjunct is a control
fixing what `liminf` computes on this codomain. -/
abbrev statement : Prop :=
  (∀ u : ℕ → ℕ∞, ∀ m : ℕ, Filter.liminf u Filter.atTop = (m : ℕ∞) →
      (∀ᶠ n in Filter.atTop, (m : ℕ∞) ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = (m : ℕ∞)))
  ∧ (∀ m : ℕ, H1 = (m : ℕ∞) → {n : ℕ | gap n = m}.Infinite)
  ∧ (∀ m : ℕ, H1 = (m : ℕ∞) → 2 ≤ m ∧ Even m)
  ∧ (∀ m : ℕ, H1 = (m : ℕ∞) →
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + m))
  ∧ (∀ B : ℕ, H1 ≤ (B : ℕ∞) →
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ B ∧ Even m ∧ {n : ℕ | gap n = m}.Infinite ∧
        ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + m))
  ∧ (Filter.liminf (fun n : ℕ => if n % 2 = 0 then (3 : ℕ∞) else 5) Filter.atTop = 3
      ∧ Filter.limsup (fun n : ℕ => if n % 2 = 0 then (3 : ℕ∞) else 5) Filter.atTop = 5)

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesH1Attained
