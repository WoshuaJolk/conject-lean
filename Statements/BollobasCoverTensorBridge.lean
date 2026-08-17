import Mathlib

/-!
# Bridge: a Bollobás set `(k,t)`-tuple modulo 2 *is* an `F₂` rank-one decomposition

This is the correspondence asserted (without proof) in O'Neill–Verstraëte,
arXiv:2011.09402v1, immediately after Definition 2:

> "there is a one to one correspondence between a modulo 2 cover of `H_{k,t}(n)` with `m`
> complete `k`-partite `k`-graphs and a Bollobás set `(k,t)`-tuple modulo 2 consisting of
> subsets of `[m]`.  Hence `f_{k,t}(n) := f'_k(H_{k,t}(n)) = min{m : b_{k,t}(m) ≥ n}`."

Stated here as an `↔` with the parameters laid out explicitly: `k` families, each indexed by
`[N]`, of subsets of the ground set `[m]`, in the orientation of **Definition 1** (`|⋂|` even
iff *fewer* than `t` indices are distinct) on the left, and on the right a decomposition of
the `(k,t)` tensor on `[N]` into exactly `m` rank-one tensors over `F₂` — the `r`-th one being
the indicator of the complete `k`-partite `k`-graph `∏_j {i : r ∈ A_{j,i}}`.

Consequence, and the reason this is filed: `f_{k,t}(N)` is the `F₂` tensor rank of `T k t N`.
Without this bridge a rank statement about `T` has no visible bearing on `b_{k,t}`, and the
flattening ceiling filed against this problem would be a fact about an unrelated matrix.

The orientation here is Definition 1's, not Conjecture 1's; the two are interchanged by
`OVParityInterchange`, which is filed alongside.
-/

namespace Statements.BollobasCoverTensorBridge

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, inside the ground set `Fin m`. -/
def kInter {k N m : ℕ} (A : Fin k → Fin N → Finset (Fin m)) (f : Fin k → Fin N) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter (fun r => ∀ j : Fin k, r ∈ A j (f j))

/-- Definition 1 of O'Neill–Verstraëte: `(A₁, …, A_k)` is a Bollobás set `(k,t)`-tuple
modulo 2 — `|⋂_j A_{j,i_j}| ≡ 0 (mod 2) ⟺ |{i₁, …, i_k}| < t`. -/
def IsBollobasTuple (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)) : Prop :=
  ∀ f : Fin k → Fin N, ((kInter A f).card % 2 = 0 ↔ (image f univ).card < t)

/-- The `(k,t)` tensor on `[N]` over `F₂`: `1` exactly when at least `t` indices are
distinct.  This is the indicator of `H_{k,t}(N)`. -/
def T (k t N : ℕ) (i : Fin k → Fin N) : ZMod 2 :=
  if t ≤ (image i univ).card then 1 else 0

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  ∀ (k t N m : ℕ) (A : Fin k → Fin N → Finset (Fin m)),
    IsBollobasTuple k t N m A ↔
      ∀ i : Fin k → Fin N,
        (∑ r : Fin m, ∏ j : Fin k, (if r ∈ A j (i j) then (1 : ZMod 2) else 0)) = T k t N i

/-- The target. -/
theorem target : statement := sorry

end Statements.BollobasCoverTensorBridge
