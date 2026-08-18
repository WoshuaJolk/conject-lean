import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice

/-!
# TwinPrimesH1Live — `H₁` is attained, `H₁` is even, and the live set really is the 123
even numbers `2, 4, …, 246`

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The gap this closes

Problem 9's progress space is a squeeze on `H₁ := liminf_{n → ∞} (p_{n+1} − p_n)`, and its
`progress_unit` asserts that *"`H₁` is even, so only the 123 even values from 2 to 246
remain live"*.  Two statements already on the problem supply the pieces: `TwinPrimesGapParity`
proves the gap sequence is even and `≥ 2` **from index 1 on**, and `TwinPrimesH1ENat` gives
`H₁` an honest `ℕ∞`-valued definition together with `2 ≤ H₁`.  Neither of them gets from
*"the sequence is eventually even"* to *"`H₁` is even"*, and `TwinPrimesGapParity` says so in
its own prose: that step is left open.

It is not a formality.  A `liminf` of an eventually-even sequence need not be even in general
— for a real-valued sequence it need not even be attained.  What rescues it here is that the
sequence is `ℕ`-valued: **a finite `liminf` of a `ℕ`-valued sequence is attained infinitely
often**, and the attaining terms inherit whatever holds eventually.  That is part (1) below,
and it is proved for an arbitrary `u : ℕ → ℕ`, not for the gap sequence, precisely so that
its hypothesis is exhibitable: `u = const 5`, `g = 5`.

## Read-back, term by term

* `gap n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n`, Mathlib's **0-indexed**
  enumeration, and `H₁ = liminf (fun n => (gap n : ℕ∞)) atTop` — the same two definitions
  `TwinPrimesH1ENat` uses, verbatim, in `ℕ∞` so that no boundedness of the gap sequence is
  assumed anywhere.
* **(1) Attainment, general.** For every `u : ℕ → ℕ` and every `g : ℕ`, if the `ℕ∞`-valued
  liminf of `u` is `g` then `g ≤ u n` eventually and `u n = g` frequently.  Both halves are
  needed: the `∀ᶠ` transports eventual properties onto `g`, the `∃ᶠ` is what makes `g` a
  value of the sequence rather than an abstract infimum.
* **(2) Specialised to the gaps.** A finite `H₁` is `≥ 2`, is **even**, and is realised by
  infinitely many *consecutive prime pairs*.  Evenness is the assertion the progress unit
  needed and did not have.
* **(3) Any finite ceiling confines `H₁`.** For every `B`, `H₁ ≤ B` forces `H₁` to be one
  even number in `[2, B]`, attained infinitely often.  Stated for an arbitrary `B` so that
  the statement does not go stale when the record improves.
* **(4) The live set, and its size.** `#{2, 4, …, 246} = 123`, checked; and `H₁ ≤ 246`
  places `H₁` in that set.  This is exactly the sentence in `progress_unit`, now a theorem
  rather than a remark.

## What is assumed, and what is not

Everything here is **unconditional**: no sieve input, no Bombieri–Vinogradov, no Zhang, no
Polymath8b.  In particular `H₁ ≤ 246` is *not* proved here and is not assumed anywhere; it
appears only as the hypothesis of (4), which is the honest way to record a consequence of an
unformalised theorem.  Nothing here bears on whether the twin prime conjecture is true.

One vacuity caveat, stated rather than hidden: the hypotheses `H₁ = g` in (2) and `H₁ ≤ B`
in (3), (4) cannot at present be discharged inside Lean, because `H₁ < ⊤` is exactly Zhang's
theorem and is unformalised.  They are satisfiable in fact, not vacuous; and the mechanism
that makes them non-vacuous — part (1) — is stated for an arbitrary `ℕ`-valued sequence,
where a witness *is* exhibitable (`u = const 5`, `g = 5`).
-/

namespace Statements.TwinPrimesH1Live

/-- The `n`-th prime gap, on Mathlib's 0-indexed `Nat.nth Nat.Prime`: `gap 0 = 3 - 2 = 1`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- `H₁`, the least gap between consecutive primes attained infinitely often, in `ℕ∞`. -/
noncomputable def H1 : ℕ∞ := Filter.liminf (fun n => (gap n : ℕ∞)) Filter.atTop

/-- The canonical proposition: a finite `ℕ∞`-valued liminf of a `ℕ`-valued sequence is a
lower bound eventually and a value frequently; hence a finite `H₁` is at least `2`, is even,
and is attained by infinitely many consecutive prime pairs; hence any ceiling `H₁ ≤ B`
confines `H₁` to an even number in `[2, B]`; and at the current record `B = 246` the live
set is the `123`-element set `{2, 4, …, 246}`. -/
abbrev statement : Prop :=
  (∀ (u : ℕ → ℕ) (g : ℕ),
      Filter.liminf (fun n => (u n : ℕ∞)) Filter.atTop = (g : ℕ∞) →
      (∀ᶠ n in Filter.atTop, g ≤ u n) ∧ (∃ᶠ n in Filter.atTop, u n = g))
  ∧ (∀ g : ℕ, H1 = (g : ℕ∞) →
      2 ≤ g ∧ Even g ∧ (∃ᶠ n in Filter.atTop, gap n = g))
  ∧ (∀ B : ℕ, H1 ≤ (B : ℕ∞) →
      ∃ g : ℕ, H1 = (g : ℕ∞) ∧ 2 ≤ g ∧ g ≤ B ∧ Even g
        ∧ (∃ᶠ n in Filter.atTop, gap n = g))
  ∧ ((Finset.image (fun i => 2 * i) (Finset.Icc 1 123)).card = 123)
  ∧ (H1 ≤ (246 : ℕ∞) →
      ∃ g : ℕ, H1 = (g : ℕ∞) ∧ g ∈ Finset.image (fun i => 2 * i) (Finset.Icc 1 123)
        ∧ (∃ᶠ n in Filter.atTop, gap n = g))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesH1Live
