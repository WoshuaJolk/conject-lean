import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
# TwinPrimesTupleBarrier — Dirichlet-level data cannot supply DHL[k,2] for any k

## The statement

For **every** finite set `H` of positive shifts, every modulus `q` and every residue `a`
coprime to `q`, there are arbitrarily large primes `p ≡ a (mod q)` such that `p + h` is
composite for **every** `h ∈ H`.

## The barrier

Fix `H`.  Let `S_H := {p : p prime and p + h composite for all h ∈ H}`.  The statement says
`S_H` meets every reduced residue class modulo every modulus infinitely often — it satisfies
the full conclusion of Dirichlet's theorem, exactly as the primes do.  And `S_H` contains no
two elements differing by any `h ∈ H`: if `p ∈ S_H` and `h ∈ H` then `p + h` is composite,
so `p + h ∉ S_H`.

Consequently no derivation whose only inputs about the primes are "an infinite set of
primes", "meets every reduced residue class mod every modulus infinitely often", or
"unbounded in every arithmetic progression" can produce **any** de Polignac-type conclusion:
not the twin prime conjecture, not infinitely many prime pairs at any fixed even distance,
and not `DHL[k,2]` for any `k`.  Each of those would be false of `S_H` for a suitable `H`,
while `S_H` has every one of the listed properties.

This matters here because `DHL[50,2]` is the single unformalised hypothesis on which the
board's route to `H₁ ≤ 246` rests, and `DHL[2,2]` at the admissible pair `{0,2}` is this
problem's root statement verbatim.  The present statement says that hypothesis provably
cannot be obtained from distributional data about the primes alone, for any `k`: it needs an
input about the *joint* behaviour of the primes and their shifts, which is what
Bombieri–Vinogradov and the Maynard–Tao sieve supply and what the parity problem then
obstructs.

## What this is NOT

Not a refutation of anything, and not evidence against the twin prime conjecture or against
`DHL[k,2]`.  The primes and `S_H` are different sets; `S_H` is the primes with the relevant
pattern-carriers deleted.  The statement is consistent with the twin prime conjecture and
with its negation.  It is also not the parity problem of Selberg, which obstructs sieve
lower bounds, is heuristic in the form usually quoted (Polymath8b §8 carries no theorem
number and is conditional on the Möbius randomness law), and separates a far stronger axiom
set than this does.

## Provenance

Folklore, and implied by Shiu's theorem on strings of congruent primes (J. London Math. Soc.
61 (2000) 359–373).  Two applications of Dirichlet's theorem: take a prime `s ≡ a (mod q)`
larger than `q` and than every element of `H`, put `L := ∏_{h ∈ H} (s + h)`, note
`gcd(s, qL) = 1`, and take any prime `p ≡ s (mod qL)` with `p > L`.  Then `(s + h) ∣ (p + h)`
with `1 < s + h < p + h`.  What is contributed is the barrier reading and the machine-checked
certificate.
-/

namespace Statements.TwinPrimesTupleBarrier

/-- For every finite set `H` of positive shifts, every modulus `q` and every residue `a`
coprime to `q`, there are arbitrarily large primes `p ≡ a (mod q)` with `p + h` composite for
every `h ∈ H`. -/
abbrev statement : Prop :=
  ∀ (H : Finset ℕ) (q a N : ℕ), 0 < q → Nat.Coprime a q → (∀ h ∈ H, 0 < h) →
    ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p ≡ a [MOD q] ∧ ∀ h ∈ H, ¬ Nat.Prime (p + h)

/-- The open target. -/
theorem target : statement := sorry

end Statements.TwinPrimesTupleBarrier
