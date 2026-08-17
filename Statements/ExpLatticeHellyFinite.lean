import Mathlib

/-!
# ExpLatticeHellyFinite

Canonical statement for the open problem of Ambrus, Balko, Frankl, Jung and Naszodi,
*On Helly numbers of exponential lattices*, European J. Combin. **116** (2024) 103884
(arXiv:2301.04683v4), section "Open problems":

> "we considered only the exponential lattice in the plane, but it would be interesting
> to obtain some estimates on the Helly numbers of exponential lattices
> {a^n : n in N_0}^d in dimension d > 2. In particular, are these numbers finite?"

Restated as Problem 1 of Arun-Dillon, *Improved Helly numbers of product sets*
(arXiv:2409.07262v2), section 5: "Is h(L_3(a)) < infinity?".

The definitions below transcribe ABFJN verbatim.  For a discrete set `S`, a convex
polytope `P` with vertices in `S` is *empty in* `S` if `P` contains no point of `S` other
than its vertices, and `h S` is the maximum number of vertices of an empty polytope.  By
Hoffman's proposition (ABFJN Proposition 1) `h S` equals the Helly number `H S` for
discrete `S`, so this is the Helly-number question.

Writing `V` for the vertex set of `P`, "every element of `V` is a vertex of `conv V`" is
exactly "no element of `V` lies in the convex hull of the others", and "`P` contains no
point of `S` other than its vertices" is `conv V` meeting `S` only inside `V`.  Both
clauses are load bearing: without the convex-position clause the whole lattice inside any
box would qualify and the answer would be trivially infinite.
-/

namespace Statements.ExpLatticeHellyFinite

/-- The exponential lattice `L_d(α) = {α ^ n : n ∈ ℕ}^d ⊆ ℝ^d`.  `ℕ` contains `0`, so
`(1, …, 1) ∈ expLattice d α`, matching ABFJN's `ℕ₀`. -/
def expLattice (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∃ n : ℕ, x i = α ^ n}

/-- `IsEmptyPolytope S V` says that `V` is the vertex set of a convex polytope that is
empty in `S`:

* `V` is finite and contained in `S`;
* every point of `V` is a vertex of `conv V`, i.e. lies outside the hull of the others;
* `conv V` contains no point of `S` beyond `V` itself. -/
def IsEmptyPolytope {d : ℕ} (S V : Set (Fin d → ℝ)) : Prop :=
  V.Finite ∧ V ⊆ S ∧
    (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
    convexHull ℝ V ∩ S ⊆ V

/-- The canonical proposition: for every base `α > 1` the number of vertices of an empty
polytope in the three-dimensional exponential lattice `L_3(α)` is bounded, i.e.
`h (L_3(α)) < ∞`.  This is Arun–Dillon Problem 1, the numbered form of the second open
problem of Ambrus–Balko–Frankl–Jung–Naszódi.

The dimension is fixed at `3`, not universally quantified over `d ≥ 3`, deliberately.
Helly numbers are monotone in the dimension (`h (L_k(α)) ≤ h (L_d(α))` for `k ≤ d`), so a
refutation here refutes the `∀ d ≥ 3` version as well, while a refutation in some large
dimension would settle the `∀ d ≥ 3` version without touching the question anybody is
asking.  A root should close only when the question closes. -/
abbrev statement : Prop :=
  ∀ α : ℝ, 1 < α →
    ∃ N : ℕ, ∀ V : Set (Fin 3 → ℝ),
      IsEmptyPolytope (expLattice 3 α) V → V.ncard ≤ N

/-- The open target.  A submission proves `statement` in its own module and the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.ExpLatticeHellyFinite
