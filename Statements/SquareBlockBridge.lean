import Commons.SetPairSystem

/-!
# SquareBlockBridge — an asymmetric block of size `m` squares to a symmetric one of size `m²`

Every `(a,b)`-bounded 1-cross intersecting set pair system of size `m` produces an
`(a+b, a+b)`-bounded one of size `m²`: multiply the system by its own mirror image
`(B, A)`, which is `(b,a)`-bounded of the same size, using ProductConstruction.

WHY THIS IS THE CHEAPEST ROUTE TO A REFUTATION OF S002.  The root bound is `5^(n/2)` for
even `n` but only `2·5^((n-1)/2)` for odd `n`, and the odd branch is weaker than the even
one by a factor `2/√5 ≈ 0.894`.  Squaring an asymmetric block lands on `n = a+b`, which can
be odd.  Working out the closure of the Füredi–Gyárfás–Király product construction over all
known blocks — `m(1,b,1) = b+1`, `m(2,2,1) = 5`, `m(2,3,1) = 7`, `m(2,n,1) =
(⌊n/2⌋+1)(⌈n/2⌉+1)` for `n ≥ 4`, `m(3,3,1) = 10` — the best product exactly equals the root
bound at every `n` from 1 to 14, with no slack anywhere.  So the minimal single new value
that would break it is, in order of search size:

* `m(3,4,1) ≥ 16`   — squares to `256 > 250 = 2·5³` at `n = 7`.  Known lower bound `15`.
* `m(4,4,1) ≥ 26`   — the target named in this problem's refutation schema, at `n = 4`.
  Known lower bound `25`.
* `m(4,5,1) ≥ 36`   — squares to `1296 > 1250 = 2·5⁴` at `n = 9`.  Known lower bound `35`.

Each of these is ONE above the product construction.  The first is the cheapest by a wide
margin: budget `3+4 = 7` and `16` pairs, against budget `8` and `26` pairs for the schema's
own target.  A `(3,4)`-bounded system of size `16` is therefore a complete refutation
certificate for S002, and this statement is the bridge that makes it one.

Read together with GroundDegreeCeiling, which says any such block must already contain a
ground element of `B`-degree at least `(m-1)/a`, so it cannot be circulant or degree-regular.
-/

namespace Statements.SquareBlockBridge

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (a b m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS a b m A B →
      ∃ A' B' : Fin (m * m) → Finset ℕ,
        Commons.OneCrossSPS (a + b) (a + b) (m * m) A' B'

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.SquareBlockBridge
