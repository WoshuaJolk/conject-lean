import Mathlib

/-!
# The diagonal instance of Conjecture 1 at `(6,5)` is exactly a `(1,1,1,1,0,0)`-town

This is the bridge from O'Neill–Verstraëte's Conjecture 1 to the `α`-town literature of
Johnston–O'Neill, Wei–Zhang–Ge and Dong–Ouyang–Wei — and it is the bridge along which the
conjecture dies.

Wei–Zhang–Ge (arXiv:2404.08280) treat the equal-families case `A₁ = ⋯ = A_k` as an instance
of Conjecture 1 ("We show the correctness of Conjecture I.1 when `A₁ = ⋯ = A_k` and `k` is a
power of 2"), so the diagonal is inside the conjecture's scope.  For a single injective
family `F` the hypothesis of Conjecture 1 at `(k,t) = (6,5)` says exactly: the intersection of
any `d` distinct members of `F` is odd for `d ≤ 4` and even for `d ∈ {5,6}`.  In the notation
of Johnston–O'Neill that is an `α`-town with `α = (1,1,1,1,0,0) ∈ F₂⁶`.

Dong–Ouyang–Wei (arXiv:2606.11139, Theorem 3) determine `f_α(n)` for every `α` from the level
and grade of its canonical decomposition.  Here `α = γ¹ + γ⁴ + γ⁵`, so `lv(α) = 2` and
`grd(α) = 2`, giving `f_α(n) = (1 + o(1)) · (2!/2)^{1/2} · n^{1/2} = (1+o(1))√n`.  Conjecture 1
at `(6,5)` asserts `m = O(n^{1/⌊6/2⌋}) = O(n^{1/3})`.  Since `√n ≫ n^{1/3}`, **Conjecture 1 is
false at `(6,5)`** — the very case its authors name as the first open one.  With
O'Neill–Verstraëte's own Lemma 6 upper bound `b_{6,5}(n) = O(n^{1/2})` this pins
`b_{6,5}(n) = Θ(n^{1/2})`.

That last step is the one thing here that is not machine-checkable from this file: it needs
Dong–Ouyang–Wei's Theorem 9 lower bound, an unrefereed June 2026 preprint whose proof I have
not verified.  The canonical decomposition `α = γ¹ + γ⁴ + γ⁵` and `lv = 2`, `grd = 2` I did
recompute independently from their definitions, and the same code returns `lv = ⌊k/2⌋` on
every case O'Neill–Verstraëte actually prove (all `t = k`, and `(5,4)`), which is the control.

What this statement contributes is the part that *can* be checked: the reduction itself.  It
is stated as an `↔`, so it carries both directions — an `α`-town of size `m` on `[n]` yields a
Conjecture 1 configuration with the same `m` and `n`, and conversely.  Anyone holding a
construction of `(1,1,1,1,0,0)`-towns of size `ω(n^{1/3})` can compose it with this and refute
the root.

Injectivity of `F` is required and is not a restriction: distinct indices with equal sets
break the `(6,5)` pattern outright once `m ≥ 6` (take `f = (i, i', x₃, x₄, x₅, x₆)` against
`f' = (i', i', x₃, …, x₆)` with `x₃ … x₆` taking three distinct values off `{i, i'}`; the
intersections coincide while the distinct-index counts are `5` and `4`).
-/

namespace Statements.DiagonalAlphaTown65

open Finset

/-- `⋂_{j=1}^{k} A_{j, f j}`, as a `Finset` of the ground set `Fin n`. -/
def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

/-- The hypothesis of Conjecture 1 at parameter `t`. -/
def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

/-- `⋂_{i ∈ s} F i`, the intersection of the members of `F` indexed by `s`. -/
def interOn {m n : ℕ} (F : Fin m → Finset (Fin n)) (s : Finset (Fin m)) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ i ∈ s, x ∈ F i)

/-- The canonical proposition: for an injective family `F`, the diagonal instance
`A₁ = ⋯ = A₆ = F` of Conjecture 1's hypothesis at `(k,t) = (6,5)` holds if and only if `F` is
an `α`-town for `α = (1,1,1,1,0,0)` — every `d`-wise intersection of distinct members is odd
for `1 ≤ d ≤ 4` and even for `d ∈ {5,6}`. -/
abbrev statement : Prop :=
  ∀ (m n : ℕ) (F : Fin m → Finset (Fin n)), Function.Injective F →
    (OVHyp 6 5 m n (fun _ i => F i) ↔
      ∀ s : Finset (Fin m), 1 ≤ s.card → s.card ≤ 6 →
        (Even (interOn F s).card ↔ 5 ≤ s.card))

/-- The target. -/
theorem target : statement := sorry

end Statements.DiagonalAlphaTown65
