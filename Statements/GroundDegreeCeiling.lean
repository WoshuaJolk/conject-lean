import Commons.SetPairSystem
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Card

/-!
# GroundDegreeCeiling — bounded ground-set degree caps the size at `a·t + 1`

Write `T e := {j | e ∈ B j}` for the set of indices whose `B`-side contains the ground
element `e`; `|T e|` is the degree of `e` in the hypergraph `B`.  If NO ground element has
`B`-degree above `t`, then an `(a,b)`-bounded `1`-cross intersecting set pair system has

    m ≤ a * t + 1.

Proof: the sets `T e`, `e ∈ A i`, partition `Fin m \ {i}` (FibreCountIdentity), so
`m - 1 = ∑_{e ∈ A i} |T e| ≤ |A i| · t ≤ a · t`.

WHAT THIS ELIMINATES.  Every construction whose ground set is "spread out" is dead as a
route to a large `(n,n)`-bounded system, because `a = t = n` gives `m ≤ n² + 1`, which is
polynomial, whereas the Füredi–Gyárfás–Király pentagon power is `5^(n/2)`.  Concretely
this kills, with a certificate rather than a failed search:

* every translation-invariant ("circulant") system `A_i = i + D_A`, `B_i = i + D_B` over a
  group of order `m` acting regularly on indices AND ground set — there every ground
  element has `B`-degree exactly `|D_B| ≤ n`, so `m ≤ n² + 1`.  This is why the
  Füredi–Gyárfás–Király cyclic example at `n = 3` has exactly `10 = 3² + 1` pairs and why
  no cyclic example can reach `26` at `n = 4`;
* every system in which `B` is a regular or near-regular hypergraph, every design-like
  construction, and every construction with `o(m)` ground-set degrees.

WHAT SURVIVES.  Any system of exponential size must contain a HUB: a ground element lying
in at least `(m-1)/a` of the sets `B_j`, a constant fraction of the whole index set when
`a = n` and `m` is exponential.  The pentagon power does exactly this — its top-level
ground elements have `B`-degree `2m/5`.  So the search for a refutation, and any proof of
the upper bound, has to engage with the hub structure; it cannot be a degree-bounded or
symmetric-design argument.  The residual is the step-2 recursion.
-/

namespace Statements.GroundDegreeCeiling

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (a b m t : ℕ) (A B : Fin m → Finset ℕ) (T : ℕ → Finset (Fin m)),
    Commons.OneCrossSPS a b m A B →
    (∀ (e : ℕ) (j : Fin m), j ∈ T e ↔ e ∈ B j) →
    (∀ e : ℕ, (T e).card ≤ t) →
    m ≤ a * t + 1

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.GroundDegreeCeiling
