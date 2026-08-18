import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# RhoCycleStructure — `ρ` is a single `k`-cycle for odd `k`, with `(k-1,k)` at distance `(k-1)/2`

This is the last hand-checked link in the Dejean-import elimination on this problem.

`TauNormalForm` proves `τ(1) = ρ` and `τ(2) = ρ∘(k-1,k)`, and that Pansiot's binary pair is
`(σ(1), σ(1)∘(1,k))`. `PansiotCycleDistanceRigidity` proves that for a pair
(`k`-cycle `c`, `c ∘ swap 0 m`) the value of `m` is a complete invariant up to sign under
simultaneous conjugacy. To connect them one needs the two facts this file supplies:

* `ρ` is a **single `k`-cycle** when `k` is odd — so the rigidity statement applies to it at all;
* inside that cycle, the two points `k-1` and `k` transposed by `τ(1)⁻¹τ(2)` sit at cyclic
  distance **`(k-1)/2`**, whereas Pansiot's `(1,k)` sits at distance **1**.

Since `(k-1)/2 ≢ ±1 (mod k)` for every odd `k ≥ 5`, the two pairs are not simultaneously
conjugate. Both facts were previously verified only computationally, for `k ≤ 61`.

## How it is stated

Rather than reasoning about cycle decompositions, the file exhibits the relabelling explicitly.
`phi` sends the letters `1,…,k` to cycle-coordinates `0,…,k-1`:

```
phi k 1 = 0 ;  phi k j = j / 2 for even j ;  phi k j = (j + k) / 2 - 1 for odd j ≥ 3
```

and the claim is that `phi` is injective on `{1,…,k}` with image in `{0,…,k-1}`, and that in
these coordinates `ρ` is exactly "add one, cyclically". A map on a `k`-element set that is
conjugate to `+1 mod k` is a single `k`-cycle, which is the content wanted. The wrap-around is
written as a two-case implication rather than with `%`, since the modulus is a variable.

The distance then falls out as arithmetic: `phi k (k-1) = (k-1)/2` because `k-1` is even, and
`phi k k = k-1` because `k` is odd, so the gap is `(k-1) - (k-1)/2 = (k-1)/2`.

Checked before stating: the closed form for `phi` was validated against the actual cycle
decomposition of `ρ` for every odd `k` in `5…299` — bijectivity, the conjugation identity at
every letter, and the distance — with a must-fail control (a `phi` off by one on odd `j`) that
is caught.
-/

namespace Statements.RhoCycleStructure

/-- `ρ`, the step-2 map. Identical to `Statements.TauNormalForm.rho`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

/-- Cycle-coordinates for `ρ`: the relabelling under which `ρ` becomes `+1 mod k`. -/
def phi (k j : ℕ) : ℕ := if j = 1 then 0 else if j % 2 = 0 then j / 2 else (j + k) / 2 - 1

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 5 ≤ k → k % 2 = 1 →
    -- `phi` lands in cycle-coordinates and is injective on the letters, hence a bijection
    (∀ j : ℕ, 1 ≤ j → j ≤ k → phi k j < k) ∧
    (∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → phi k i = phi k j → i = j) ∧
    -- in those coordinates `ρ` is `+1` cyclically, so `ρ` is a single `k`-cycle
    (∀ j : ℕ, 1 ≤ j → j ≤ k → phi k j + 1 = k → phi k (rho k j) = 0) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k → phi k j + 1 < k → phi k (rho k j) = phi k j + 1) ∧
    -- and the transposed pair `(k-1, k)` sits at cyclic distance `(k-1)/2`
    (phi k (k - 1) = (k - 1) / 2 ∧ phi k k = k - 1 ∧ phi k k - phi k (k - 1) = (k - 1) / 2)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.RhoCycleStructure
