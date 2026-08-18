import Mathlib.Analysis.SpecialFunctions.Sqrt
import Commons.PaleyLocalizationTheta

/-!
# PaleyLocRegular — the Paley 1-localization is `(p-5)/4`-regular on `(p-1)/2` vertices

The vertex count and the degree of `G_{p,1}` are quoted constantly and are pinned on this
problem only at `p = 13` and `p = 17`, as finite decidable checks
(`Statements.PaleyLocSmallCases`).  This is the general statement, for every prime
`p ≡ 1 (mod 4)`.

Both numbers are stated multiplied out so that no natural-number subtraction or division
appears: `2·|V| = p - 1` and `8·(#ordered adjacent pairs) = (p-1)(p-5)`, over `ℝ`.  Since the
graph is vertex-transitive the second is equivalent to every vertex having degree `(p-5)/4`.

The proof is a character-sum computation.  Writing `χ` for the quadratic character of
`ZMod p`, the indicator of the nonzero squares is `(χ(x)² + χ(x))/2`, so
`4·∑_{u,v ∈ Q} χ(u-v)` expands into four sums over all of `ZMod p`, of which two vanish by
`∑ₓ χ(x) = 0` and two contribute `-(p-1)` each: the second pair via `χ(-1) = 1`, the fourth
via the Jacobi sum `∑ₛ χ(s)χ(1-s) = -1`.  Hence `∑_{u,v ∈ Q} χ(u-v) = -(p-1)/2 = -|V|`, and
the edge count follows because adjacency of distinct `u, v ∈ Q` is `(1 + χ(u-v))/2`.

The vertex count itself is `∑ₐ χ(a) = 0` again.
-/

namespace Statements.PaleyLocRegular

/-- The canonical proposition: `2|V| = p-1` and `8·#(ordered adjacent pairs) = (p-1)(p-5)`. -/
abbrev statement : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, p % 4 = 1 →
    haveI : NeZero p := NeZero.of_pos hp.pos
    2 * (Fintype.card (Commons.PaleyLocV p) : ℝ) = (p : ℝ) - 1 ∧
      8 * (Fintype.card {q : Commons.PaleyLocV p × Commons.PaleyLocV p //
          Commons.paleyLocAdj p q.1 q.2} : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) - 5)

theorem target : statement := sorry

end Statements.PaleyLocRegular
