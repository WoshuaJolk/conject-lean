import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.List.Basic

/-!
# UPBCyclicFamily224k — one explicit family that should settle every `k ≥ 3`

This statement pins a single explicit integer family and asserts that every member of it is
an unextendible product basis. It is the `MinUPB224kMinus1` existence problem with the search
removed: what is left is verification, not construction.

Writing `M` for the number of blocks past the base, the family has `n = 14 + 4M` states in
`C² ⊗ C² ⊗ C^d` with `d = 11 + 4M`; that is `k = M + 3`, `n = 4k+2`, `d = 4k−1`. So this
statement covers exactly `k ≥ 3`; `k = 2` is `MinUPB227`, which is already proved.

## Where the family comes from

`M = 0` is the `k = 3` member, built from the verified `k = 2` witness by one block insertion.
Each further member is obtained by a **local surgery** that adds four states and four
dimensions:

* pick two `w`-orthogonality (matching) edges whose four endpoints induce a 4-cycle in the
  graph `F` of pairs that are allowed to be non-orthogonal in the third factor;
* add vectors `ε_A, ε_B, ε_C, ε_D` in the new `C⁴` to those four old states, cutting the two
  matching edges;
* give the four **new** states the *dual basis* `ε*_A, ε*_B, ε*_C, ε*_D` of the `ε`'s.

The new block's Gram matrix is then exactly `G⁻¹`, where `G` is the Gram matrix of the `ε`'s,
so the two orthogonalities forced inside a block (`⟨A,B⟩ = ⟨C,D⟩ = 0`, because those pairs
share a `u`-direction and are not matched) become `(G⁻¹)₁₂ = (G⁻¹)₃₄ = 0` — two polynomial
conditions on `G`. Solving them, with the free parameter `q = −2`, gives

```
ε_A = (1,0,0,0)   ε_B = (0,1,0,0)   ε_C = (−2,−1,1,0)   ε_D = (−1,2,0,1)
ε*_A = (1,0,2,1)  ε*_B = (0,1,1,−2) ε*_C = (0,0,1,0)    ε*_D = (0,0,0,1)
```

and that is the whole of `eA … sD` below. Every entry of every third factor is an integer of
absolute value at most 12, uniformly in `k`.

The 4-cycle requirement is not decoration. On a path-shaped set of four endpoints the two
conditions force `G` to split into two 2×2 blocks, `G⁻¹` splits with it, and the block loses
the edges `A–C` and `B–D`; the resulting graph has maximum degree 2 in the bulk, which makes
the space of linear relations among the third factors collapse onto two long paths and
destroys unextendibility. That is why the `4k+2` states have to be wired as a **cycle** of
`k` blocks with the two leftover states spliced into one wrap-around channel, and not as a
path — the same reason `d ≡ 3 (mod 4)` is harder than `d ≡ 1 (mod 4)`.

## Why one expects it to be true

Unextendibility here is equivalent to a statement about `4k+2` points in `P²`. For nonzero
`a : C²` the annihilated states form one `u`-parallel class, for nonzero `b` one `w`-class,
so with `T = A ∪ B` (at most 3 indices) the condition is that `{zᵢ : i ∉ T}` spans `C^d`.
Dually: let `Y` be a `3 × n` matrix whose rows span the space of linear relations among the
`zᵢ` (there are exactly 3, since the rank is `d = n − 3`). Then that condition says the
columns `Y_T` are linearly independent.

Under the surgery `Y` transforms by `Y_{X_K} = −Σ_Z G_{ZX} Y_{n_Z}`, and because the
insertion site repeats, the new columns are **affine-linear in the block index** `m`:

```
A_m = A₀ + m(2Q − P)          B_m = −C₀ − 2A₀ + (2m−1)Q
C_m = C₀ + m(2P − 6Q)         D_m = −2C₀ − 6A₀ + (2m−1)P
```

with `P = Y₁`, `Q = Y₂`. Every required independence is therefore a determinant polynomial
in `m` (or in `m, m'`) with fixed rational coefficients, and each one is nonzero at every
positive integer for an elementary reason — for instance `det[C_m, D_m, A_{m'}] ∝ 42m − 40m' − 3`
is odd on the left and even on the right, and `det[C_m, D_m, B_{m'}] ∝ 12m² − 12mm' + 24m − 22m' + 17`
is odd for all integers.

## What is machine-checked at pose time, and what is not

Checked in Lean, by `decide` on the integer form of the definitions below: the family is a
pairwise-orthogonal product set for `M = 0,1,2,3,4,5` (that is `k = 3 … 8`).
Checked in exact rational arithmetic outside Lean: orthogonality, rank `= 4k−1`, and all
`(2k+3)(4k+3)` spanning conditions, for every `k` from 3 to 36.
**Not** checked by any kernel: the general `M`. That is exactly what this statement asks for.

A proof splits cleanly into (i) orthogonality, a finite case analysis on window adjacency —
every inner product in the family is `M`-independent — and (ii) unextendibility, the
determinant polynomials above.
-/

namespace Statements.UPBCyclicFamily224k

def Zb : ℕ → ℕ → ℤ := fun i s =>
  ((([[0, 0, -6, -5, 1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
     [5, -4, -2, 0, 0, 0, 0, -2, 12, 1, 0],
     [0, -3, 6, 1, 1, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, -1, 1, -6, 1, 0, 0, 0, 0],
     [0, 2, 2, -3, -3, 0, 0, 0, 1, 0, 0],
     [12, 12, 6, -6, 6, 0, 0, -12, -2, 0, -1],
     [0, 1, -2, 3, 3, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, -1, -6, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, -12],
     [0, 0, 0, 0, 0, 0, 0, 0, 1, -12, -2],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD i []).getD s 0)

def eA : ℕ → ℤ := fun t => ([1, 0, 0, 0] : List ℤ).getD t 0
def eB : ℕ → ℤ := fun t => ([0, 1, 0, 0] : List ℤ).getD t 0
def eC : ℕ → ℤ := fun t => ([-2, -1, 1, 0] : List ℤ).getD t 0
def eD : ℕ → ℤ := fun t => ([-1, 2, 0, 1] : List ℤ).getD t 0
def sA : ℕ → ℤ := fun t => ([1, 0, 2, 1] : List ℤ).getD t 0
def sB : ℕ → ℤ := fun t => ([0, 1, 1, -2] : List ℤ).getD t 0
def sC : ℕ → ℤ := fun t => ([0, 0, 1, 0] : List ℤ).getD t 0
def sD : ℕ → ℤ := fun t => ([0, 0, 0, 1] : List ℤ).getD t 0

/-- The four new third-factors introduced by one block insertion, as a table. -/
def dual (tt t : ℕ) : ℤ :=
  if tt = 0 then sA t else if tt = 1 then sB t else if tt = 2 then sC t else sD t

/-- Third factor `s` of state `i`, for the member of the family with `M` blocks past
the base, i.e. `k = M + 3`, `n = 14 + 4M`, `d = 11 + 4M`. -/
def ZI (M i s : ℕ) : ℤ :=
  if s < 11 then Zb i s
  else
    let m := (s - 11) / 4
    let t := (s - 11) % 4
    if i = 1 then eA t
    else if i = 2 then eC t
    else if i = 10 then (if m = 0 then eD t else 0)
    else if i = 12 then (if m = 0 then eB t else 0)
    else if i < 14 then 0
    else
      let mm := (i - 14) / 4
      let tt := (i - 14) % 4
      if mm = m then dual tt t
      else if m = mm + 1 then (if tt = 0 then eD t else if tt = 2 then eB t else 0)
      else 0

/-- The `u`-parallel class of state `i`. Classes `2p` and `2p+1` are orthogonal to each other. -/
def clsI (i : ℕ) : ℕ :=
  if i < 14 then ([0,0,1,1,2,2,3,3,4,5,6,6,7,7] : List ℕ).getD i 0
  else 8 + 2 * ((i - 14) / 4) + ((i - 14) % 4) / 2

/-- First factor of state `i`. -/
def UI (i r : ℕ) : ℤ :=
  let c := clsI i
  let p : ℤ := (c / 2 : ℕ) + 1
  if c % 2 = 0 then (if r = 0 then 1 else p) else (if r = 0 then -p else 1)

/-- The index of the `w`-orthogonality pair containing state `i`. -/
def wpI (M i : ℕ) : ℕ :=
  if i < 14 then
    (if i = 10 then (if M = 0 then 5 else 10)
     else if i = 12 then (if M = 0 then 6 else 9)
     else ([0,5,6,1,2,3,4,1,0,2,0,3,0,4] : List ℕ).getD i 0)
  else
    let mm := (i - 14) / 4
    let tt := (i - 14) % 4
    if tt = 0 then (if mm + 1 = M then 5 else 12 + 2 * mm)
    else if tt = 1 then 9 + 2 * mm
    else if tt = 2 then (if mm + 1 = M then 6 else 11 + 2 * mm)
    else 10 + 2 * mm

/-- Which side of its `w`-orthogonality pair state `i` sits on. -/
def wsI (i : ℕ) : ℕ :=
  if i < 14 then (if i ≤ 6 then 0 else 1)
  else (if (i - 14) % 4 = 0 ∨ (i - 14) % 4 = 2 then 1 else 0)

/-- Second factor of state `i`. -/
def WI (M i r : ℕ) : ℤ :=
  let p : ℤ := (wpI M i : ℕ) + 1
  if wsI i = 0 then (if r = 0 then 1 else p) else (if r = 0 then -p else 1)

/-- The canonical proposition. For every `M`, the explicit family
`(UI, WI M, ZI M)` is an unextendible product basis of cardinality `14 + 4M` in
`C² ⊗ C² ⊗ C^(11 + 4M)`; equivalently, the `k = M + 3` case of `MinUPB224kMinus1`
is witnessed by this family. -/
abbrev statement : Prop :=
  ∀ M : ℕ,
    ∀ u : Fin (14 + 4 * M) → Fin 2 → ℂ,
    ∀ w : Fin (14 + 4 * M) → Fin 2 → ℂ,
    ∀ z : Fin (14 + 4 * M) → Fin (11 + 4 * M) → ℂ,
      u = (fun i r => ((UI i.val r.val : ℤ) : ℂ)) →
      w = (fun i r => ((WI M i.val r.val : ℤ) : ℂ)) →
      z = (fun i r => ((ZI M i.val r.val : ℤ) : ℂ)) →
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
        ∀ c : Fin (11 + 4 * M) → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UPBCyclicFamily224k
