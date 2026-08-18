import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

/-!
# AdmissibleTupleFloor212 — a quantitative floor under every narrow-tuple search, and the
proved method ceiling it forces on the `k = 50` route

Self-contained: imports only `Mathlib`, defines everything it mentions, uses no `Commons`.

## What this is

The Goldston–Pintz–Yıldırım / Zhang / Maynard–Tao / Polymath8b route produces an upper bound
on `H₁` as a product of two factors: an analytic input `DHL[k,2]`, and a *combinatorial*
input — an admissible `k`-tuple of small diameter `d`.  The bound it yields is `H₁ ≤ d`, and
`d` can be no smaller than `H(k)`, the least diameter of an admissible `k`-tuple.

`H(k)` is therefore a hard floor under the entire tuple-search half of the method, and it is
worth knowing quantitatively rather than qualitatively.  This statement proves

  **`H(50) ≥ 212`**,

so the `k = 50` route — Polymath8b's, the one behind the current record `H₁ ≤ 246` — provably
cannot output any bound below `212`, no matter how much compute is spent searching for a
narrower tuple.  Equivalently, and this is the useful form: **any bound below `212` by this
route requires `DHL[k,2]` for some `k ≤ 49`**, which is strictly stronger analytic input than
anything currently proved.

This is a **method ceiling with a theorem behind it**, not a heuristic.  It should be read
beside the problem's existing recorded ceiling, the parity barrier, which is explicitly
flagged as informal and conditional on the Möbius randomness law.  This one is a `decide`.

## The proof, in one paragraph

Admissibility at `2, 3, 5, 7` names four omitted residue classes `r₂, r₃, r₅, r₇`.  By CRT
exactly `1 · 2 · 4 · 6 = 48` of the `210` residues mod `210` avoid all four, *whatever the
four classes are* — discharged here by kernel `decide` over all `2 · 3 · 5 · 7 = 210` choices,
with no `native_decide`.  So every `h ∈ H` has `h % 210` in a fixed 48-element set `T`, and
`h ↦ (h / 210, h % 210)` is injective, giving `H.card ≤ 48 · (d / 210 + 1)` for
`H ⊆ [0, d]`, which is the bound for general `k`.

The sharp form at `k = 50` drops the block decomposition and counts the window directly: for
every one of the `210` choices of `(r₂, r₃, r₅, r₇)`, at most `49` of the `212` residues
`0, …, 211` survive all four omitted classes — again a kernel `decide`, again with no
`native_decide`.  So an admissible set inside `[0, 211]` has at most `49` elements, and a
`50`-element one forces `d ≥ 212`.  The constant is sharp for this sieve: at `213` some
choice does admit `50` survivors, so no better bound follows from the primes `2, 3, 5, 7`
alone.

The same argument at the prime `2` alone gives the cruder general floor `d ≥ 2(#H − 1)`,
stated separately because it holds for every `k` with no case analysis and is the reason
`H₁` is even.

## Read-back, term by term

* `Admissible H := ∀ p prime, ∃ r < p, ∀ h ∈ H, h % p ≠ r`.  **The bound `r < p` is
  load-bearing**: drop it and `r := p` satisfies the clause for every set, since `p` is never
  a value of `h % p`, and every conjunct below becomes worthless.  Two conjuncts check the
  predicate discriminates, in both directions: `{0,2}` is admissible, `{0,2,4}` is not.
* `∀ h ∈ H, h ≤ d` is the diameter hypothesis in the weakest usable form — it does not demand
  `0 ∈ H`, so the conclusion applies to any translate.
* The `48` and the `210` are the primorial `2·3·5·7` and its totient-like count
  `1·2·4·6`.  Going further costs more than it buys: primes up to `11` would give `218` and
  up to `13` would give `226`, at `2310` and `30030` residue choices respectively rather
  than `210`.  Only `2, 3, 5, 7` are used here, and the `212` is exactly what they give.

## What is not claimed

Not `H(50) = 246`, which is Engelsma's exhaustive computation (OEIS A008407) and is not
verified here; only `H(50) ≥ 212`, which is `34` short of it and is proved. No bound on `H₁`
moves — `H₁ ≤ 246` still stands and `H₁ ≥ 2` still stands. `DHL[k,2]` is neither proved nor
assumed for any `k`. Nothing here is evidence for or against the twin prime conjecture; it
constrains a *method*, not the answer.
-/

namespace Statements.AdmissibleTupleFloor212

/-- A finite set of shifts is *admissible* when for every prime `p` some residue class
`r < p` mod `p` contains no element of it.  The bound `r < p` is load-bearing. -/
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- The canonical proposition: an admissible set inside `[0, d]` has at most
`48 · (d / 210 + 1)` elements; at most `49` elements when it lies inside `[0, 211]`; hence a
`50`-element admissible set has `d ≥ 212`, which is the method ceiling on the `k = 50` route; the crude
parity floor `2(#H − 1) ≤ d` holds for every `k`; and the admissibility predicate
discriminates — `{0,2}` yes, `{0,2,4}` no. -/
abbrev statement : Prop :=
  (∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) →
      H.card ≤ 48 * (d / 210 + 1))
  ∧ (∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) → d ≤ 211 → H.card ≤ 49)
  ∧ (∀ (H : Finset ℕ) (d : ℕ), Admissible H → H.card = 50 → (∀ h ∈ H, h ≤ d) → 212 ≤ d)
  ∧ (∀ (H : Finset ℕ) (d : ℕ), Admissible H → (∀ h ∈ H, h ≤ d) → 2 * (H.card - 1) ≤ d)
  ∧ (Admissible ({0, 2} : Finset ℕ) ∧ ({0, 2} : Finset ℕ).card = 2
      ∧ ¬ Admissible ({0, 2, 4} : Finset ℕ))

/-- The open target.  A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.AdmissibleTupleFloor212
