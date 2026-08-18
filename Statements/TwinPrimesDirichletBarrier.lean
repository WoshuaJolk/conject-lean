import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
# TwinPrimesDirichletBarrier — Dirichlet-level data cannot force twin primes

## The barrier, in words

Let `S := {p : p is prime and p + 2 is composite}` — the primes that are **not** the lower
member of a twin prime pair.  The first conjunct below says that `S` satisfies the full
conclusion of Dirichlet's theorem on primes in arithmetic progressions: for every modulus
`q` and every residue `a` coprime to `q`, `S` contains infinitely many primes `p ≡ a (mod q)`.
By its definition `S` contains no twin-prime lower member whatsoever.

So `S` is an infinite set of primes which is unbounded in every reduced residue class modulo
every modulus, and which has no twin pairs at all.  Consequently **any** derivation of the
twin prime conjecture whose only inputs about the primes are of that shape — "an infinite
set of primes", "meets every reduced residue class mod every modulus infinitely often",
"unbounded in every arithmetic progression" — would prove a false statement about `S`, and
is therefore not a valid derivation.  Dirichlet-level distributional information about the
primes, however completely it is exploited, provably cannot settle the twin prime conjecture.

## What this is NOT

It is not a refutation, and it does not make the twin prime conjecture less likely.  The
primes and `S` are different sets: `S` is the primes with the twin lower members deleted.
Both conjuncts below are consistent with the twin prime conjecture and with its negation.
The content is about **proofs**, not about the truth of the conjecture.

It is also not the parity problem.  Selberg's parity obstruction concerns sieve *lower*
bounds and is, in the form usually quoted (Polymath8b §8), heuristic and conditional on the
Möbius randomness law; it carries no theorem number.  The present statement separates a much
weaker axiom set, and it is a theorem.

## The strengthened second conjunct

The second conjunct says the failure is not marginal and is not special to the shift `2`:
in every arithmetic progression `a mod q`, for every shift `h ≥ 1` and every depth `k`,
there are infinitely many primes `p` for which **all** of `p + h, p + 2h, …, p + kh` are
composite.  So de Polignac's conjecture for any fixed gap is equally out of reach of this
data, and the certificate for `2` is one instance of a uniform phenomenon.

## Provenance of the mathematics

The second conjunct is folklore: pick a prime `s > max(kh, q)` with `s ≡ a (mod q)` by
Dirichlet, set `L := ∏_{j=1}^{k} (s + jh)`, note `gcd(s, qL) = 1` because `s` is a prime
exceeding every `jh`, and apply Dirichlet again to the progression `s mod qL`.  Any prime
`p ≡ s (mod qL)` with `p > L` has `(s + jh) ∣ (p + jh)` and `1 < s + jh < p + jh`.  It is
implied by, and enormously weaker than, Shiu's theorem on strings of congruent primes
(J. London Math. Soc. 61 (2000) 359–373).  What is recorded here is the barrier reading,
with the certificate exhibited and machine-checked.
-/

namespace Statements.TwinPrimesDirichletBarrier

/-- Dirichlet-level distributional data about the primes cannot imply the twin prime
conjecture: the primes `p` with `p + 2` composite already meet every reduced residue class
modulo every modulus infinitely often, and the same holds with `p + h, …, p + kh` all
composite for every shift `h` and every depth `k`. -/
abbrev statement : Prop :=
  (∀ q a N : ℕ, 0 < q → Nat.Coprime a q →
      ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ ¬ Nat.Prime (p + 2) ∧ p ≡ a [MOD q])
  ∧ (∀ q a h k N : ℕ, 0 < q → 0 < h → Nat.Coprime a q →
      ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p ≡ a [MOD q] ∧
        ∀ j : ℕ, 0 < j → j ≤ k → ¬ Nat.Prime (p + h * j))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.TwinPrimesDirichletBarrier
