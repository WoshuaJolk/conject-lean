import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.List.Basic

/-!
# UPBCyclicFamilyOrth224k — the cyclic family is an orthogonal product set, for every k

This is the first half of `UPBCyclicFamily224k`, separated so it can be settled on its own:
the explicit family pinned there really is a set of `14 + 4M` pairwise-orthogonal nonzero
product states in `C² ⊗ C² ⊗ C^(11 + 4M)` — that is, cardinality `4k+2` in
`C² ⊗ C² ⊗ C^(4k−1)` with `k = M + 3`, for every `k ≥ 4`. Unextendibility, the hard half, is
NOT claimed here; it stays with `UPBCyclicFamily224k`.

The definitions below are character-for-character the ones in `UPBCyclicFamily224k`, so the
two statements are about the same family and a proof of the harder one subsumes this.

## Why it is not automatic

`ZI` does not depend on `M` at all — only the range of indices does — so the family is a
single infinite configuration truncated in two places at once. Every inner product in it is
therefore `M`-independent, and orthogonality is a finite case analysis on *window adjacency*:
two states can fail to be orthogonal in the third factor only if their 4-coordinate windows
meet. The bookkeeping is: states `1` and `2` carry a component in every window; states `10`
and `12` in window `0` only; the `A` and `C` of block `m` in windows `m` and `m+1`; the `B`
and `D` of block `m` in window `m` only. Pairs whose windows are disjoint are orthogonal for
free; the rest are covered by a `u`-parallel class, a `w`-parallel class, or a cancellation
between two adjacent windows — the last being where `⟨ε_A, ε^*_A⟩ = 1` is cancelled by
`⟨ε_A, ε_D⟩ = −1`, and likewise `⟨ε_C, ε^*_C⟩ = 1` by `⟨ε_C, ε_B⟩ = −1`.

`1 ≤ M` is assumed because at `M = 0` the `w`-pairing degenerates: states `10` and `12` are
then matched to `1` and `2` directly rather than to the first inserted block. `M = 0` is the
`k = 3` case and is `MinUPB2211`, already proved.
-/

namespace Statements.UPBCyclicFamilyOrth224k


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


/-- The canonical proposition: for every `M ≥ 1` the pinned family is a set of `14 + 4M`
nonzero, pairwise orthogonal product states in `C² ⊗ C² ⊗ C^(11 + 4M)`. -/
abbrev statement : Prop :=
  ∀ M : ℕ, 1 ≤ M →
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
        (∑ r, star (z i r) * z j r) = 0)

/-- The open target. A submission proves `statement` in its own module. -/
theorem target : statement := sorry

end Statements.UPBCyclicFamilyOrth224k
