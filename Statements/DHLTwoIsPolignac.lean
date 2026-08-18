import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# DHLTwoIsPolignac — the `k = 2` endpoint of the Maynard–Tao route overshoots the target

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## The correction this makes

The Goldston–Pintz–Yıldırım / Maynard–Tao route proves `H₁ ≤ d` from `DHL[k,2]` plus an
admissible `k`-tuple of diameter `d`.  Running `k` down to `2` with the tuple `{0,2}` gives
`H₁ ≤ 2`, hence the twin prime conjecture — so it is natural, and wrong, to read the whole
route as "the twin prime conjecture is `DHL[2,2]`".

`DHL[k,2]` is **uniform over all admissible `k`-tuples**; that is how it is stated in the
literature and how it must be stated for the reduction to be usable at `k = 50`, where no
particular tuple is privileged.  This statement proves what that uniformity costs at `k = 2`:

* an admissible pair is **exactly** a pair with even difference — nothing else is required,
  because for every prime `p ≥ 3` a two-element set misses a class automatically, and at
  `p = 2` admissibility is precisely equal parity;
* therefore `DHL[2,2]` is **equivalent to de Polignac's conjecture**: *every* even number
  occurs infinitely often as a gap between two primes, not merely as a gap between
  consecutive ones.

De Polignac is strictly stronger than the twin prime conjecture, which is only its `h = 2`
instance.  So the route cannot deliver `H₁ = 2` through its own `k = 2` endpoint without
simultaneously delivering every even `h`: the last step of the ladder proves more than the
thing it was aimed at.  Two of the extra consequences, `h = 4` and `h = 6`, are recorded
explicitly so that the overshoot is visible in the proposition itself and not only in prose.

This is not a claim that the twin prime conjecture is unreachable.  It is a claim about where
the target sits relative to the method's own endpoint, and it identifies precisely what a
non-uniform variant would have to be: `DHL[2,2]` **restricted to the single tuple `{0,2}`**,
which is the root statement of this problem verbatim and is therefore not a reduction at all.

## Read-back, term by term

* `Admissible H := ∀ p prime, ∃ r < p, ∀ h ∈ H, h % p ≠ r`.  The bound `r < p` is
  load-bearing: without it `r := p` satisfies the clause for every set.  Controls in both
  directions are carried in the statement: `{0,2}` is admissible, `{0,3}` is not.
* `DHL2 k := ∀ H, H.card = k → Admissible H → ∀ N, ∃ n > N, 2 ≤ #{h ∈ H | n + h prime}`,
  the same definition used by `TwinPrimesDHLReduction` on this problem.
* The first conjunct is an `↔` for **all** `a < b`, not just for `a = 0`: admissibility is
  translation-invariant and the statement is proved in the translated generality the
  equivalence with de Polignac needs.
* `Even (b - a)` uses truncated natural subtraction, harmless under the `a < b` hypothesis
  carried in the same conjunct.

## What is not claimed

`DHL[2,2]` is neither proved nor assumed; it appears only as one side of an equivalence and
as the hypothesis of three implications.  De Polignac's conjecture is not proved.  No bound
on `H₁` moves, and no progress snapshot accompanies this.  Nothing here bears on whether the
twin prime conjecture is true.
-/

namespace Statements.DHLTwoIsPolignac

/-- Admissibility, with the load-bearing `r < p`. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- `DHL[k,2]`, uniform over admissible `k`-tuples, as in the Maynard–Tao / Polymath8b
literature. -/
def DHL2 (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → Admissible H →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 2 ≤ (H.filter (fun h => Nat.Prime (n + h))).card

/-- The canonical proposition: an admissible pair is exactly an even-difference pair;
`DHL[2,2]` is exactly de Polignac's conjecture; it implies the twin prime conjecture in the
form this problem's root takes, and also the `h = 4` and `h = 6` cases, which the twin prime
conjecture does not give; and the admissibility predicate discriminates. -/
abbrev statement : Prop :=
  (∀ a b : ℕ, a < b → (Admissible ({a, b} : Finset ℕ) ↔ Even (b - a)))
  ∧ (DHL2 2 ↔ ∀ h : ℕ, 0 < h → Even h →
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime n ∧ Nat.Prime (n + h))
  ∧ (DHL2 2 → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
  ∧ (DHL2 2 → (∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 4))
            ∧ (∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 6)))
  ∧ (Admissible ({0, 2} : Finset ℕ) ∧ ¬ Admissible ({0, 3} : Finset ℕ))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.DHLTwoIsPolignac
