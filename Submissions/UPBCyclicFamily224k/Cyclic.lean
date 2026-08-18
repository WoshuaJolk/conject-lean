import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The cyclic family is an unextendible product basis, for every `k = M + 3`

This closes `UPBCyclicFamily224k`, and with it the terminal case of `MinUPB224kMinus1`:
for every `k ≥ 3` there is an unextendible product basis of cardinality `4k + 2` in
`C² ⊗ C² ⊗ C^(4k-1)`.

## Orthogonality

`ZG` does not mention `M`, so the family is one infinite configuration cut off in two places
and every inner product is `M`-independent. Splitting a third factor into an 11-coordinate
base part and `M` windows of four gives
`⟨zᵢ, zⱼ⟩ = Σ_{s<11} Zb i s · Zb j s + Σ_{m<M} EIP i j m`, and for each pair one of the three
factors vanishes: a `u`-parallel class for two states of one block in orthogonal classes; a
`w`-parallel class for the seven matched base pairs, the two long edges `(1, A_{M-1})`,
`(2, C_{M-1})` and the inter-block edges `(A_m, D_{m+1})`, `(C_m, B_{m+1})`; and otherwise
`⟨zᵢ, zⱼ⟩ = 0`, either termwise or by the two-window cancellations
`⟨ε_A, ε*_A⟩ + ⟨ε_A, ε_D⟩ = 1 + (−1) = 0` and `⟨ε_C, ε*_C⟩ + ⟨ε_C, ε_B⟩ = 1 + (−1) = 0`.
That is `orthAll` (`orthGen` for `M ≥ 1`, one `decide` for `M = 0`).

## Unextendibility

Dually. `YI` is a `3 × (14+4M)` integer matrix with `Y · Z = 0` (`YZ`), and `L · Z = 18 · I`
on the base block together with the window inversion gives injectivity of `Z` (`injAll`).
Because the columns of `YI` for a new state are **affine-linear in the block index**,

```
A_m = A₀ + m(2Q − P)      B_m = −C₀ − 2A₀ + (2m−1)Q
C_m = C₀ + m(2P − 6Q)     D_m = −2C₀ − 6A₀ + (2m−1)P
```

every independence condition is a determinant polynomial in `m` (or `m, m'`) with fixed
coefficients, and each is nonzero at every positive integer for an elementary reason:
`det[C_m, D_m, A_{m'}] ∝ 42m − 40m' − 3` is odd, `det[C_m, D_m, B_{m'}] ∝
12m² − 12mm' + 24m − 22m' + 17` is odd, `det[A_m, B_m, C_{m'}] ∝ 2m² − 2mm' + 17m − 18m' − 2`
factors as `(2m+18)(m'−m+1) = m+16` which has no positive integer solution, and the rest are
linear in `m − m'`.

Given nonzero `a`, the states annihilated by `a` in the first factor form one `u`-parallel
class, which has at most two members (`cp k`, `cq k`); given nonzero `b`, the states
annihilated in the second factor form one `w`-class, a singleton, because the map
`i ↦ (wpI M i, wsI i)` is injective (`wpInjAll`). So at most three of the numbers `⟨zᵢ, c⟩`
are nonzero, their index set lies in `{cp k₀, cq k₀, j₀}`, and the three relations
`Σ_i Y r i ⟨zᵢ, c⟩ = 0` form a `3 × 3` system with nonzero determinant (`mainDet`), or a
`2 × 2` system of full rank for the two singleton classes `{8}`, `{9}` (`minorDet`). Hence
every `⟨zᵢ, c⟩` vanishes and `injAll` forces `c = 0`.

Every entry of every factor is an integer of absolute value at most 12, uniformly in `k`.
-/

namespace Submissions.UPBCyclicFamily224k.Cyclic


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

def dual (tt t : ℕ) : ℤ :=
  if tt = 0 then sA t else if tt = 1 then sB t else if tt = 2 then sC t else sD t

/-- Window entry: coordinate `t` of the window-`m` part of state `i`. -/
def EW (i m t : ℕ) : ℤ :=
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

/-- Third factor `s` of state `i`. Note this does not depend on the number of blocks. -/
def ZG (i s : ℕ) : ℤ :=
  if s < 11 then Zb i s else EW i ((s - 11) / 4) ((s - 11) % 4)

lemma ZG_base (i s : ℕ) (hs : s < 11) : ZG i s = Zb i s := by
  simp [ZG, hs]

lemma ZG_win' (i m t : ℕ) (ht : t < 4) : ZG i (11 + 4 * m + t) = EW i m t := by
  have h1 : ¬ (11 + 4 * m + t < 11) := by omega
  have h2 : (11 + 4 * m + t - 11) = 4 * m + t := by omega
  have h3 : (4 * m + t) / 4 = m := by omega
  have h4 : (4 * m + t) % 4 = t := by omega
  simp [ZG, h1, h2, h3, h4]

lemma ZG_win0 (i m : ℕ) : ZG i (11 + 4 * m) = EW i m 0 := by
  have h1 : ¬ (11 + 4 * m < 11) := by omega
  have h2 : (11 + 4 * m - 11) = 4 * m := by omega
  have h3 : (4 * m) / 4 = m := by omega
  have h4 : (4 * m) % 4 = 0 := by omega
  simp [ZG, h1, h2, h3, h4]

lemma ZG_win1 (i m : ℕ) : ZG i (11 + (4 * m + 1)) = EW i m 1 := by
  have h1 : ¬ (11 + (4 * m + 1) < 11) := by omega
  have h2 : (11 + (4 * m + 1) - 11) = 4 * m + 1 := by omega
  have h3 : (4 * m + 1) / 4 = m := by omega
  have h4 : (4 * m + 1) % 4 = 1 := by omega
  simp [ZG, h1, h2, h3, h4]

lemma ZG_win2 (i m : ℕ) : ZG i (11 + (4 * m + 2)) = EW i m 2 := by
  have h1 : ¬ (11 + (4 * m + 2) < 11) := by omega
  have h2 : (11 + (4 * m + 2) - 11) = 4 * m + 2 := by omega
  have h3 : (4 * m + 2) / 4 = m := by omega
  have h4 : (4 * m + 2) % 4 = 2 := by omega
  simp [ZG, h1, h2, h3, h4]

lemma ZG_win3 (i m : ℕ) : ZG i (11 + (4 * m + 3)) = EW i m 3 := by
  have h1 : ¬ (11 + (4 * m + 3) < 11) := by omega
  have h2 : (11 + (4 * m + 3) - 11) = 4 * m + 3 := by omega
  have h3 : (4 * m + 3) / 4 = m := by omega
  have h4 : (4 * m + 3) % 4 = 3 := by omega
  simp [ZG, h1, h2, h3, h4]

lemma sum_blocks (g : ℕ → ℤ) : ∀ M : ℕ,
    ∑ s ∈ Finset.range (4 * M), g s
      = ∑ m ∈ Finset.range M, (g (4*m) + g (4*m+1) + g (4*m+2) + g (4*m+3)) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    have h4 : 4 * (M + 1) = 4 * M + 4 := by ring
    rw [h4, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    simp [Finset.sum_range_succ]

/-- The inner product of two third factors splits into a base part and one term per window. -/
lemma ipz_split (M i j : ℕ) :
    (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s)
      = (∑ s ∈ Finset.range 11, Zb i s * Zb j s)
        + ∑ m ∈ Finset.range M,
            (EW i m 0 * EW j m 0 + EW i m 1 * EW j m 1
              + EW i m 2 * EW j m 2 + EW i m 3 * EW j m 3) := by
  have hsplit := Finset.sum_range_add (fun s => ZG i s * ZG j s) 11 (4 * M)
  rw [hsplit]
  have hA : (∑ s ∈ Finset.range 11, ZG i s * ZG j s)
      = ∑ s ∈ Finset.range 11, Zb i s * Zb j s :=
    Finset.sum_congr rfl fun s hs => by
      rw [ZG_base i s (Finset.mem_range.mp hs), ZG_base j s (Finset.mem_range.mp hs)]
  have hB : (∑ s ∈ Finset.range (4 * M), ZG i (11 + s) * ZG j (11 + s))
      = ∑ m ∈ Finset.range M,
          (EW i m 0 * EW j m 0 + EW i m 1 * EW j m 1
            + EW i m 2 * EW j m 2 + EW i m 3 * EW j m 3) := by
    rw [sum_blocks (fun s => ZG i (11 + s) * ZG j (11 + s)) M]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ZG_win0 i m, ZG_win0 j m, ZG_win1 i m, ZG_win1 j m,
        ZG_win2 i m, ZG_win2 j m, ZG_win3 i m, ZG_win3 j m]
  rw [hA, hB]

def EIP (i j m : ℕ) : ℤ :=
  EW i m 0 * EW j m 0 + EW i m 1 * EW j m 1 + EW i m 2 * EW j m 2 + EW i m 3 * EW j m 3

lemma ipz_eq (M i j : ℕ) :
    (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s)
      = (∑ s ∈ Finset.range 11, Zb i s * Zb j s) + ∑ m ∈ Finset.range M, EIP i j m := by
  rw [ipz_split]; rfl

/-- The window contribution of an old state that is not one of the four surgery sites. -/
lemma EW_old (i m t : ℕ) (h : i < 14) (h1 : i ≠ 1) (h2 : i ≠ 2) (h10 : i ≠ 10) (h12 : i ≠ 12) :
    EW i m t = 0 := by
  simp [EW, h, h1, h2, h10, h12]

lemma EW_new (mm tt m t : ℕ) (htt : tt < 4) :
    EW (14 + 4 * mm + tt) m t =
      (if mm = m then dual tt t
       else if m = mm + 1 then (if tt = 0 then eD t else if tt = 2 then eB t else 0)
       else 0) := by
  have hn1 : 14 + 4 * mm + tt ≠ 1 := by omega
  have hn2 : 14 + 4 * mm + tt ≠ 2 := by omega
  have hn10 : 14 + 4 * mm + tt ≠ 10 := by omega
  have hn12 : 14 + 4 * mm + tt ≠ 12 := by omega
  have hn14 : ¬ (14 + 4 * mm + tt < 14) := by omega
  have hd : (14 + 4 * mm + tt - 14) = 4 * mm + tt := by omega
  have hq : (4 * mm + tt) / 4 = mm := by omega
  have hr : (4 * mm + tt) % 4 = tt := by omega
  simp [EW, hn1, hn2, hn10, hn12, hn14, hd, hq, hr]

lemma EIP_zero_old (i j m : ℕ) (h : i < 14) (h1 : i ≠ 1) (h2 : i ≠ 2) (h10 : i ≠ 10)
    (h12 : i ≠ 12) : EIP i j m = 0 := by
  simp [EIP, EW_old i m 0 h h1 h2 h10 h12, EW_old i m 1 h h1 h2 h10 h12,
        EW_old i m 2 h h1 h2 h10 h12, EW_old i m 3 h h1 h2 h10 h12]

lemma sum_all_zero (f : ℕ → ℤ) (M : ℕ) (h : ∀ m, f m = 0) :
    ∑ m ∈ Finset.range M, f m = 0 := Finset.sum_eq_zero fun m _ => h m

lemma sum_one (f : ℕ → ℤ) (a M : ℕ) (ha : a < M) (h : ∀ m, m ≠ a → f m = 0) :
    ∑ m ∈ Finset.range M, f m = f a := by
  rw [Finset.sum_eq_single a]
  · intro b _ hb; exact h b hb
  · intro hb; exact absurd (Finset.mem_range.mpr ha) hb

lemma sum_two (f : ℕ → ℤ) (a M : ℕ) (ha : a + 1 < M)
    (h : ∀ m, m ≠ a → m ≠ a + 1 → f m = 0) :
    ∑ m ∈ Finset.range M, f m = f a + f (a + 1) := by
  have hsub : ({a, a + 1} : Finset ℕ) ⊆ Finset.range M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun x _ hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact h x hx.1 hx.2)]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]


/-- The window correction to the base inner product, for two old states. -/
def corrOld (i j : ℕ) : ℤ :=
  if (i = 1 ∧ j = 10) ∨ (i = 10 ∧ j = 1) ∨ (i = 2 ∧ j = 12) ∨ (i = 12 ∧ j = 2) then -1
  else if (i = 10 ∧ j = 12) ∨ (i = 12 ∧ j = 10) then 2
  else 0

lemma EW_10 (m t : ℕ) (hm : m ≠ 0) : EW 10 m t = 0 := by simp [EW, hm]
lemma EW_12 (m t : ℕ) (hm : m ≠ 0) : EW 12 m t = 0 := by simp [EW, hm]

lemma EIP_zero_of_10 (j m : ℕ) (hm : m ≠ 0) : EIP 10 j m = 0 := by
  simp [EIP, EW_10 m 0 hm, EW_10 m 1 hm, EW_10 m 2 hm, EW_10 m 3 hm]
lemma EIP_zero_of_12 (j m : ℕ) (hm : m ≠ 0) : EIP 12 j m = 0 := by
  simp [EIP, EW_12 m 0 hm, EW_12 m 1 hm, EW_12 m 2 hm, EW_12 m 3 hm]

lemma EIP_symm (i j m : ℕ) : EIP i j m = EIP j i m := by
  simp [EIP]; ring

lemma EIPsum_old (M i j : ℕ) (hM : 1 ≤ M) (hi : i < 14) (hj : j < 14)
    (h12 : ¬ (i = 1 ∧ j = 2)) (h21 : ¬ (i = 2 ∧ j = 1)) (hij : i ≠ j) :
    ∑ m ∈ Finset.range M, EIP i j m = corrOld i j := by
  by_cases hia : i = 1 ∨ i = 2 ∨ i = 10 ∨ i = 12
  · by_cases hja : j = 1 ∨ j = 2 ∨ j = 10 ∨ j = 12
    · have key : ∀ m, m ≠ 0 → EIP i j m = 0 := by
        intro m hm
        rcases hia with h | h | h | h
        · rcases hja with g | g | g | g
          · exact absurd (h.trans g.symm) hij
          · exact absurd ⟨h, g⟩ h12
          · subst g; rw [EIP_symm]; exact EIP_zero_of_10 i m hm
          · subst g; rw [EIP_symm]; exact EIP_zero_of_12 i m hm
        · rcases hja with g | g | g | g
          · exact absurd ⟨h, g⟩ h21
          · exact absurd (h.trans g.symm) hij
          · subst g; rw [EIP_symm]; exact EIP_zero_of_10 i m hm
          · subst g; rw [EIP_symm]; exact EIP_zero_of_12 i m hm
        · subst h; exact EIP_zero_of_10 j m hm
        · subst h; exact EIP_zero_of_12 j m hm
      rw [sum_one _ 0 M hM key]
      rcases hia with h | h | h | h <;> rcases hja with g | g | g | g <;> subst h <;> subst g <;>
        first
          | (exact absurd rfl hij)
          | (exact absurd ⟨rfl, rfl⟩ h12)
          | (exact absurd ⟨rfl, rfl⟩ h21)
          | decide
    · push_neg at hja
      have hz : ∀ m, EIP i j m = 0 := by
        intro m
        rw [EIP_symm]
        exact EIP_zero_old j i m hj hja.1 hja.2.1 hja.2.2.1 hja.2.2.2
      rw [sum_all_zero _ M hz]
      simp only [corrOld]
      obtain ⟨a1, a2, a3, a4⟩ := hja
      split
      · omega
      · split
        · omega
        · rfl
  · push_neg at hia
    have hz : ∀ m, EIP i j m = 0 := fun m => EIP_zero_old i j m hi hia.1 hia.2.1 hia.2.2.1 hia.2.2.2
    rw [sum_all_zero _ M hz]
    simp only [corrOld]
    obtain ⟨a1, a2, a3, a4⟩ := hia
    split
    · omega
    · split
      · omega
      · rfl


def clsI (i : ℕ) : ℕ :=
  if i < 14 then ([0,0,1,1,2,2,3,3,4,5,6,6,7,7] : List ℕ).getD i 0
  else 8 + 2 * ((i - 14) / 4) + ((i - 14) % 4) / 2

def UI (i r : ℕ) : ℤ :=
  let c := clsI i
  let p : ℤ := (c / 2 : ℕ) + 1
  if c % 2 = 0 then (if r = 0 then 1 else p) else (if r = 0 then -p else 1)

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

def wsI (i : ℕ) : ℕ :=
  if i < 14 then (if i ≤ 6 then 0 else 1)
  else (if (i - 14) % 4 = 0 ∨ (i - 14) % 4 = 2 then 1 else 0)

def WI (M i r : ℕ) : ℤ :=
  let p : ℤ := (wpI M i : ℕ) + 1
  if wsI i = 0 then (if r = 0 then 1 else p) else (if r = 0 then -p else 1)

def ipu (i j : ℕ) : ℤ := UI i 0 * UI j 0 + UI i 1 * UI j 1
def ipw (M i j : ℕ) : ℤ := WI M i 0 * WI M j 0 + WI M i 1 * WI M j 1

lemma wsI_cases (i : ℕ) : wsI i = 0 ∨ wsI i = 1 := by
  unfold wsI
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma ipu_zero (i j : ℕ) (hp : clsI i / 2 = clsI j / 2) (hpar : clsI i % 2 ≠ clsI j % 2) :
    ipu i j = 0 := by
  simp only [ipu, UI]
  rcases Nat.even_or_odd (clsI i) with h | h
  · have h0 : clsI i % 2 = 0 := Nat.even_iff.mp h
    have h1 : clsI j % 2 = 1 := by omega
    simp [h0, h1, hp]
  · have h0 : clsI i % 2 = 1 := Nat.odd_iff.mp h
    have h1 : clsI j % 2 = 0 := by omega
    simp [h0, h1, hp]

lemma ipw_zero (M i j : ℕ) (hp : wpI M i = wpI M j) (hs : wsI i ≠ wsI j) :
    ipw M i j = 0 := by
  simp only [ipw, WI]
  rcases wsI_cases i with h | h <;> rcases wsI_cases j with g | g
  · exact absurd (h.trans g.symm) hs
  · simp [h, g, hp]
  · simp [h, g, hp]
  · exact absurd (h.trans g.symm) hs


lemma EW_1 (m t : ℕ) : EW 1 m t = eA t := by simp [EW]
lemma EW_2 (m t : ℕ) : EW 2 m t = eC t := by simp [EW]
lemma EW_10e (m t : ℕ) : EW 10 m t = (if m = 0 then eD t else 0) := by simp [EW]
lemma EW_12e (m t : ℕ) : EW 12 m t = (if m = 0 then eB t else 0) := by simp [EW]

lemma EIP_1 (j m : ℕ) : EIP 1 j m = EW j m 0 := by
  simp only [EIP, EW_1]; norm_num [eA]

lemma EIP_2 (j m : ℕ) : EIP 2 j m = -2 * EW j m 0 - EW j m 1 + EW j m 2 := by
  simp only [EIP, EW_2]; norm_num [eC]; ring

lemma EIP_10z (j m : ℕ) : EIP 10 j m
    = (if m = 0 then -EW j 0 0 + 2 * EW j 0 1 + EW j 0 3 else 0) := by
  by_cases h : m = 0
  · subst h; simp only [EIP, EW_10e]; norm_num [eD]
  · simp only [EIP, EW_10e, if_neg h]; norm_num

lemma EIP_12z (j m : ℕ) : EIP 12 j m = (if m = 0 then EW j 0 1 else 0) := by
  by_cases h : m = 0
  · subst h; simp only [EIP, EW_12e, if_pos rfl]; norm_num [eB]
  · simp only [EIP, EW_12e, if_neg h]; norm_num

lemma EW_new0 (mm tt m : ℕ) (htt : tt < 4) :
    EW (14 + 4 * mm + tt) m 0
      = (if mm = m then (if tt = 0 then 1 else 0)
         else if m = mm + 1 then (if tt = 0 then -1 else 0) else 0) := by
  rw [EW_new mm tt m 0 htt]
  interval_cases tt <;> norm_num [dual, sA, sB, sC, sD, eD, eB]

lemma EW_new1 (mm tt m : ℕ) (htt : tt < 4) :
    EW (14 + 4 * mm + tt) m 1
      = (if mm = m then (if tt = 1 then 1 else 0)
         else if m = mm + 1 then (if tt = 0 then 2 else if tt = 2 then 1 else 0) else 0) := by
  rw [EW_new mm tt m 1 htt]
  interval_cases tt <;> norm_num [dual, sA, sB, sC, sD, eD, eB]

lemma EW_new2 (mm tt m : ℕ) (htt : tt < 4) :
    EW (14 + 4 * mm + tt) m 2
      = (if mm = m then (if tt = 0 then 2 else if tt = 1 then 1 else if tt = 2 then 1 else 0)
         else 0) := by
  rw [EW_new mm tt m 2 htt]
  interval_cases tt <;> norm_num [dual, sA, sB, sC, sD, eD, eB]

lemma EW_new3 (mm tt m : ℕ) (htt : tt < 4) :
    EW (14 + 4 * mm + tt) m 3
      = (if mm = m then (if tt = 0 then 1 else if tt = 1 then -2 else if tt = 3 then 1 else 0)
         else if m = mm + 1 then (if tt = 0 then 1 else 0) else 0) := by
  rw [EW_new mm tt m 3 htt]
  interval_cases tt <;> norm_num [dual, sA, sB, sC, sD, eD, eB]


-- ### window sums for an old state against a new state

lemma sum1_new_ne0 (M mm tt : ℕ) (htt : tt < 4) (h : tt ≠ 0) :
    ∑ m ∈ Finset.range M, EIP 1 (14 + 4 * mm + tt) m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_1, EW_new0 mm tt m htt]
  by_cases h1 : mm = m
  · simp [h1, h]
  · by_cases h2 : m = mm + 1 <;> simp [h1, h2, h]

lemma sum1_new_A (M mm : ℕ) (hM : mm + 1 < M) :
    ∑ m ∈ Finset.range M, EIP 1 (14 + 4 * mm + 0) m = 0 := by
  rw [sum_two _ mm M hM ?_]
  · rw [EIP_1, EIP_1, EW_new0 mm 0 mm (by norm_num), EW_new0 mm 0 (mm + 1) (by norm_num)]
    norm_num
  · intro m h1 h2
    rw [EIP_1, EW_new0 mm 0 m (by norm_num)]
    simp [Ne.symm h1, h2]

lemma sum2_new_ne2 (M mm tt : ℕ) (htt : tt < 4) (h : tt ≠ 2) :
    ∑ m ∈ Finset.range M, EIP 2 (14 + 4 * mm + tt) m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_2, EW_new0 mm tt m htt, EW_new1 mm tt m htt, EW_new2 mm tt m htt]
  by_cases h1 : mm = m
  · subst h1
    interval_cases tt <;> simp_all <;> norm_num
  · by_cases h2 : m = mm + 1
    · interval_cases tt <;>
        first
          | (exact absurd rfl h)
          | (simp [h1, h2]; norm_num)
          | simp [h1, h2]
    · simp [h1, h2]

lemma sum2_new_C (M mm : ℕ) (hM : mm + 1 < M) :
    ∑ m ∈ Finset.range M, EIP 2 (14 + 4 * mm + 2) m = 0 := by
  rw [sum_two _ mm M hM ?_]
  · rw [EIP_2, EIP_2,
      EW_new0 mm 2 mm (by norm_num), EW_new1 mm 2 mm (by norm_num), EW_new2 mm 2 mm (by norm_num),
      EW_new0 mm 2 (mm+1) (by norm_num), EW_new1 mm 2 (mm+1) (by norm_num),
      EW_new2 mm 2 (mm+1) (by norm_num)]
    norm_num
  · intro m h1 h2
    rw [EIP_2, EW_new0 mm 2 m (by norm_num), EW_new1 mm 2 m (by norm_num),
      EW_new2 mm 2 m (by norm_num)]
    simp [Ne.symm h1, h2]

lemma sum10_new (M mm tt : ℕ) (htt : tt < 4) (h : ¬ (mm = 0 ∧ tt = 3)) :
    ∑ m ∈ Finset.range M, EIP 10 (14 + 4 * mm + tt) m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_10z]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, EW_new0 mm tt 0 htt, EW_new1 mm tt 0 htt, EW_new3 mm tt 0 htt]
    by_cases h0 : mm = 0
    · subst h0
      interval_cases tt <;> simp_all <;> norm_num
    · simp [h0, Nat.succ_ne_zero]
  · simp [hm]

lemma sum12_new (M mm tt : ℕ) (htt : tt < 4) (h : ¬ (mm = 0 ∧ tt = 1)) :
    ∑ m ∈ Finset.range M, EIP 12 (14 + 4 * mm + tt) m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_12z]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, EW_new1 mm tt 0 htt]
    by_cases h0 : mm = 0
    · subst h0
      interval_cases tt <;> simp_all
    · simp [h0, Nat.succ_ne_zero]
  · simp [hm]


-- ### window sums for two new states

lemma EIP_nn (mm tt mm' tt' m : ℕ) (htt : tt < 4) (htt' : tt' < 4) :
    EIP (14 + 4 * mm + tt) (14 + 4 * mm' + tt') m =
      (if mm = m then (if tt = 0 then 1 else 0) else if m = mm + 1 then (if tt = 0 then -1 else 0) else 0)
        * (if mm' = m then (if tt' = 0 then 1 else 0) else if m = mm' + 1 then (if tt' = 0 then -1 else 0) else 0)
    + (if mm = m then (if tt = 1 then 1 else 0) else if m = mm + 1 then (if tt = 0 then 2 else if tt = 2 then 1 else 0) else 0)
        * (if mm' = m then (if tt' = 1 then 1 else 0) else if m = mm' + 1 then (if tt' = 0 then 2 else if tt' = 2 then 1 else 0) else 0)
    + (if mm = m then (if tt = 0 then 2 else if tt = 1 then 1 else if tt = 2 then 1 else 0) else 0)
        * (if mm' = m then (if tt' = 0 then 2 else if tt' = 1 then 1 else if tt' = 2 then 1 else 0) else 0)
    + (if mm = m then (if tt = 0 then 1 else if tt = 1 then -2 else if tt = 3 then 1 else 0) else if m = mm + 1 then (if tt = 0 then 1 else 0) else 0)
        * (if mm' = m then (if tt' = 0 then 1 else if tt' = 1 then -2 else if tt' = 3 then 1 else 0) else if m = mm' + 1 then (if tt' = 0 then 1 else 0) else 0) := by
  unfold EIP
  rw [EW_new0 mm tt m htt, EW_new0 mm' tt' m htt', EW_new1 mm tt m htt, EW_new1 mm' tt' m htt',
      EW_new2 mm tt m htt, EW_new2 mm' tt' m htt', EW_new3 mm tt m htt, EW_new3 mm' tt' m htt']

lemma sumnn_same (M mm tt tt' : ℕ) (htt : tt < 4) (htt' : tt' < 4)
    (h : (tt = 0 ∧ tt' = 1) ∨ (tt = 1 ∧ tt' = 0) ∨ (tt = 2 ∧ tt' = 3) ∨ (tt = 3 ∧ tt' = 2)) :
    ∑ m ∈ Finset.range M, EIP (14 + 4 * mm + tt) (14 + 4 * mm + tt') m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_nn mm tt mm tt' m htt htt']
  by_cases ha : mm = m
  · subst ha
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> norm_num
  · by_cases hb : m = mm + 1
    · subst hb
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
        simp only [if_neg ha, if_pos rfl] <;> norm_num
    · simp only [if_neg ha, if_neg hb]
      norm_num

lemma sumnn_adj (M mm tt tt' : ℕ) (htt : tt < 4) (htt' : tt' < 4)
    (h1 : ¬ (tt = 0 ∧ tt' = 3)) (h2 : ¬ (tt = 2 ∧ tt' = 1)) :
    ∑ m ∈ Finset.range M, EIP (14 + 4 * mm + tt) (14 + 4 * (mm + 1) + tt') m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_nn mm tt (mm + 1) tt' m htt htt']
  by_cases hb : m = mm + 1
  · subst hb
    have e1 : ¬ (mm = mm + 1) := by omega
    simp only [if_neg e1, if_pos rfl]
    interval_cases tt <;> interval_cases tt' <;>
      first
        | (exact absurd ⟨rfl, rfl⟩ h1)
        | (exact absurd ⟨rfl, rfl⟩ h2)
        | norm_num
  · by_cases ha : mm = m
    · have e2 : ¬ (mm + 1 = m) := by omega
      have e3 : ¬ (m = mm + 1 + 1) := by omega
      simp only [if_neg e2, if_neg e3]
      norm_num
    · simp only [if_neg ha, if_neg hb]
      norm_num

lemma sumnn_far (M mm tt mm' tt' : ℕ) (htt : tt < 4) (htt' : tt' < 4)
    (h : mm + 1 < mm' ∨ mm' + 1 < mm) :
    ∑ m ∈ Finset.range M, EIP (14 + 4 * mm + tt) (14 + 4 * mm' + tt') m = 0 := by
  refine sum_all_zero _ M (fun m => ?_)
  rw [EIP_nn mm tt mm' tt' m htt htt']
  rcases h with h | h
  · by_cases ha : mm = m
    · have e1 : ¬ (mm' = m) := by omega
      have e2 : ¬ (m = mm' + 1) := by omega
      simp only [if_neg e1, if_neg e2]
      norm_num
    · by_cases hb : m = mm + 1
      · have e1 : ¬ (mm' = m) := by omega
        have e2 : ¬ (m = mm' + 1) := by omega
        simp only [if_neg e1, if_neg e2]
        norm_num
      · simp only [if_neg ha, if_neg hb]
        norm_num
  · by_cases ha : mm' = m
    · have e1 : ¬ (mm = m) := by omega
      have e2 : ¬ (m = mm + 1) := by omega
      simp only [if_neg e1, if_neg e2]
      norm_num
    · by_cases hb : m = mm' + 1
      · have e1 : ¬ (mm = m) := by omega
        have e2 : ¬ (m = mm + 1) := by omega
        simp only [if_neg e1, if_neg e2]
        norm_num
      · simp only [if_neg ha, if_neg hb]
        norm_num


-- ### index bookkeeping

lemma Zb_big (i s : ℕ) (h : 14 ≤ i) : Zb i s = 0 := by
  unfold Zb
  have hl : ([[0, 0, -6, -5, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
     [5, -4, -2, 0, 0, 0, 0, -2, 12, 1, 0], [0, -3, 6, 1, 1, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, -1, 1, -6, 1, 0, 0, 0, 0], [0, 2, 2, -3, -3, 0, 0, 0, 1, 0, 0],
     [12, 12, 6, -6, 6, 0, 0, -12, -2, 0, -1], [0, 1, -2, 3, 3, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, -1, -6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, -12], [0, 0, 0, 0, 0, 0, 0, 0, 1, -12, -2],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).length ≤ i := by simp; omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]

lemma decomp (M i : ℕ) (h : i < 14 + 4 * M) :
    i < 14 ∨ ∃ mm tt, mm < M ∧ tt < 4 ∧ i = 14 + 4 * mm + tt := by
  by_cases hc : i < 14
  · exact Or.inl hc
  · refine Or.inr ⟨(i - 14) / 4, (i - 14) % 4, by omega, by omega, by omega⟩

lemma clsI_new (mm tt : ℕ) (htt : tt < 4) : clsI (14 + 4 * mm + tt) = 8 + 2 * mm + tt / 2 := by
  have h1 : ¬ (14 + 4 * mm + tt < 14) := by omega
  have h2 : (14 + 4 * mm + tt - 14) = 4 * mm + tt := by omega
  have h3 : (4 * mm + tt) / 4 = mm := by omega
  have h4 : (4 * mm + tt) % 4 = tt := by omega
  simp [clsI, h1, h2, h3, h4]

lemma wpI_old (M i : ℕ) (hM : 1 ≤ M) (hi : i < 14) : wpI M i = wpI 1 i := by
  have h : ¬ (M = 0) := by omega
  simp [wpI, hi, h]

lemma wpI_new (M mm tt : ℕ) (htt : tt < 4) :
    wpI M (14 + 4 * mm + tt) =
      (if tt = 0 then (if mm + 1 = M then 5 else 12 + 2 * mm)
       else if tt = 1 then 9 + 2 * mm
       else if tt = 2 then (if mm + 1 = M then 6 else 11 + 2 * mm)
       else 10 + 2 * mm) := by
  have h1 : ¬ (14 + 4 * mm + tt < 14) := by omega
  have h2 : (14 + 4 * mm + tt - 14) = 4 * mm + tt := by omega
  have h3 : (4 * mm + tt) / 4 = mm := by omega
  have h4 : (4 * mm + tt) % 4 = tt := by omega
  simp [wpI, h1, h2, h3, h4]

lemma wsI_new (mm tt : ℕ) (htt : tt < 4) :
    wsI (14 + 4 * mm + tt) = (if tt = 0 ∨ tt = 2 then 1 else 0) := by
  have h1 : ¬ (14 + 4 * mm + tt < 14) := by omega
  have h2 : (14 + 4 * mm + tt - 14) = 4 * mm + tt := by omega
  have h4 : (4 * mm + tt) % 4 = tt := by omega
  simp [wsI, h1, h2, h4]

lemma ipz_new_base (M i j : ℕ) (hj : 14 ≤ j) :
    (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s) = ∑ m ∈ Finset.range M, EIP i j m := by
  rw [ipz_eq]
  have : (∑ s ∈ Finset.range 11, Zb i s * Zb j s) = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [Zb_big j s hj]; ring
  rw [this, zero_add]


-- ### assembly

lemma ipw_old_eq (M i j : ℕ) (hM : 1 ≤ M) (hi : i < 14) (hj : j < 14) :
    ipw M i j = ipw 1 i j := by
  simp only [ipw, WI, wpI_old M i hM hi, wpI_old M j hM hj]

lemma oo_dec : ∀ i ∈ Finset.range 14, ∀ j ∈ Finset.range 14, i ≠ j →
    ¬(i = 1 ∧ j = 2) → ¬(i = 2 ∧ j = 1) →
    (ipu i j = 0 ∨ ipw 1 i j = 0 ∨
      (∑ s ∈ Finset.range 11, Zb i s * Zb j s) + corrOld i j = 0) := by decide

lemma case_OO (M i j : ℕ) (hM : 1 ≤ M) (hi : i < 14) (hj : j < 14) (hij : i ≠ j) :
    ipu i j = 0 ∨ ipw M i j = 0 ∨
      (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s) = 0 := by
  by_cases h12 : i = 1 ∧ j = 2
  · left; obtain ⟨a, b⟩ := h12; subst a; subst b; decide
  by_cases h21 : i = 2 ∧ j = 1
  · left; obtain ⟨a, b⟩ := h21; subst a; subst b; decide
  have hz : (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s)
      = (∑ s ∈ Finset.range 11, Zb i s * Zb j s) + corrOld i j := by
    rw [ipz_eq, EIPsum_old M i j hM hi hj h12 h21 hij]
  rcases oo_dec i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj) hij h12 h21 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by rw [ipw_old_eq M i j hM hi hj]; exact h))
  · exact Or.inr (Or.inr (by rw [hz]; exact h))

lemma case_ON (M i mm tt : ℕ) (hM : 1 ≤ M) (hi : i < 14) (hmm : mm < M) (htt : tt < 4) :
    ipw M i (14 + 4 * mm + tt) = 0 ∨
      (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG (14 + 4 * mm + tt) s) = 0 := by
  rw [ipz_new_base M i (14 + 4 * mm + tt) (by omega)]
  have hws : wsI (14 + 4 * mm + tt) = (if tt = 0 ∨ tt = 2 then 1 else 0) := wsI_new mm tt htt
  have hwp := wpI_new M mm tt htt
  by_cases hi1 : i = 1
  · subst hi1
    by_cases ht : tt = 0
    · subst ht
      by_cases hlast : mm + 1 = M
      · left
        refine ipw_zero M 1 _ ?_ ?_
        · have h5 : wpI 1 1 = 5 := by decide
          rw [wpI_old M 1 hM (by norm_num), h5, hwp]
          norm_num [hlast]
        · rw [hws]; simp [wsI]
      · exact Or.inr (sum1_new_A M mm (by omega))
    · exact Or.inr (sum1_new_ne0 M mm tt htt ht)
  · by_cases hi2 : i = 2
    · subst hi2
      by_cases ht : tt = 2
      · subst ht
        by_cases hlast : mm + 1 = M
        · left
          refine ipw_zero M 2 _ ?_ ?_
          · have h6 : wpI 1 2 = 6 := by decide
            rw [wpI_old M 2 hM (by norm_num), h6, hwp]
            norm_num [hlast]
          · rw [hws]; simp [wsI]
        · exact Or.inr (sum2_new_C M mm (by omega))
      · exact Or.inr (sum2_new_ne2 M mm tt htt ht)
    · by_cases hi10 : i = 10
      · subst hi10
        by_cases hd : mm = 0 ∧ tt = 3
        · obtain ⟨a, b⟩ := hd; subst a; subst b
          left
          refine ipw_zero M 10 _ ?_ ?_
          · have h10 : wpI 1 10 = 10 := by decide
            rw [wpI_old M 10 hM (by norm_num), h10, hwp]
            norm_num
          · rw [hws]; simp [wsI]
        · exact Or.inr (sum10_new M mm tt htt hd)
      · by_cases hi12 : i = 12
        · subst hi12
          by_cases hd : mm = 0 ∧ tt = 1
          · obtain ⟨a, b⟩ := hd; subst a; subst b
            left
            refine ipw_zero M 12 _ ?_ ?_
            · have h9 : wpI 1 12 = 9 := by decide
              rw [wpI_old M 12 hM (by norm_num), h9, hwp]
              norm_num
            · rw [hws]; simp [wsI]
          · exact Or.inr (sum12_new M mm tt htt hd)
        · exact Or.inr (sum_all_zero _ M
            (fun m => EIP_zero_old i _ m hi hi1 hi2 hi10 hi12))


lemma ipu_symm (i j : ℕ) : ipu i j = ipu j i := by simp only [ipu]; ring
lemma ipw_symm (M i j : ℕ) : ipw M i j = ipw M j i := by simp only [ipw]; ring
lemma ipz_symm (M i j : ℕ) :
    (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s)
      = ∑ s ∈ Finset.range (11 + 4 * M), ZG j s * ZG i s :=
  Finset.sum_congr rfl fun s _ => by ring

lemma case_NN (M mm tt mm' tt' : ℕ) (hmm : mm < M) (hmm' : mm' < M)
    (htt : tt < 4) (htt' : tt' < 4) (hne : ¬ (mm = mm' ∧ tt = tt')) :
    ipu (14 + 4 * mm + tt) (14 + 4 * mm' + tt') = 0 ∨
    ipw M (14 + 4 * mm + tt) (14 + 4 * mm' + tt') = 0 ∨
      (∑ s ∈ Finset.range (11 + 4 * M),
        ZG (14 + 4 * mm + tt) s * ZG (14 + 4 * mm' + tt') s) = 0 := by
  rw [ipz_new_base M _ _ (by omega)]
  rcases lt_trichotomy mm mm' with h | h | h
  · by_cases hadj : mm' = mm + 1
    · subst hadj
      by_cases hw1 : tt = 0 ∧ tt' = 3
      · obtain ⟨a, b⟩ := hw1; subst a; subst b
        refine Or.inr (Or.inl (ipw_zero M _ _ ?_ ?_))
        · rw [wpI_new M mm 0 (by norm_num), wpI_new M (mm + 1) 3 (by norm_num)]
          have : ¬ (mm + 1 = M) := by omega
          simp [this]; omega
        · rw [wsI_new mm 0 (by norm_num), wsI_new (mm + 1) 3 (by norm_num)]; norm_num
      · by_cases hw2 : tt = 2 ∧ tt' = 1
        · obtain ⟨a, b⟩ := hw2; subst a; subst b
          refine Or.inr (Or.inl (ipw_zero M _ _ ?_ ?_))
          · rw [wpI_new M mm 2 (by norm_num), wpI_new M (mm + 1) 1 (by norm_num)]
            have : ¬ (mm + 1 = M) := by omega
            simp [this]; omega
          · rw [wsI_new mm 2 (by norm_num), wsI_new (mm + 1) 1 (by norm_num)]; norm_num
        · exact Or.inr (Or.inr (sumnn_adj M mm tt tt' htt htt' hw1 hw2))
    · exact Or.inr (Or.inr (sumnn_far M mm tt mm' tt' htt htt' (Or.inl (by omega))))
  · subst h
    by_cases hc : tt / 2 = tt' / 2
    · refine Or.inr (Or.inr (sumnn_same M mm tt tt' htt htt' ?_))
      have htne : tt ≠ tt' := fun e => hne ⟨rfl, e⟩
      interval_cases tt <;> interval_cases tt' <;> simp_all
    · refine Or.inl (ipu_zero _ _ ?_ ?_)
      · rw [clsI_new mm tt htt, clsI_new mm tt' htt']; omega
      · rw [clsI_new mm tt htt, clsI_new mm tt' htt']; omega
  · by_cases hadj : mm = mm' + 1
    · subst hadj
      by_cases hw1 : tt' = 0 ∧ tt = 3
      · obtain ⟨a, b⟩ := hw1; subst a; subst b
        refine Or.inr (Or.inl (ipw_zero M _ _ ?_ ?_))
        · rw [wpI_new M (mm' + 1) 3 (by norm_num), wpI_new M mm' 0 (by norm_num)]
          have : ¬ (mm' + 1 = M) := by omega
          simp [this]; omega
        · rw [wsI_new (mm' + 1) 3 (by norm_num), wsI_new mm' 0 (by norm_num)]; norm_num
      · by_cases hw2 : tt' = 2 ∧ tt = 1
        · obtain ⟨a, b⟩ := hw2; subst a; subst b
          refine Or.inr (Or.inl (ipw_zero M _ _ ?_ ?_))
          · rw [wpI_new M (mm' + 1) 1 (by norm_num), wpI_new M mm' 2 (by norm_num)]
            have : ¬ (mm' + 1 = M) := by omega
            simp [this]; omega
          · rw [wsI_new (mm' + 1) 1 (by norm_num), wsI_new mm' 2 (by norm_num)]; norm_num
        · refine Or.inr (Or.inr ?_)
          rw [Finset.sum_congr rfl (fun m _ => EIP_symm _ _ m)]
          exact sumnn_adj M mm' tt' tt htt' htt hw1 hw2
    · exact Or.inr (Or.inr (sumnn_far M mm tt mm' tt' htt htt' (Or.inr (by omega))))

theorem orthGen (M : ℕ) (hM : 1 ≤ M) (i j : ℕ) (hi : i < 14 + 4 * M) (hj : j < 14 + 4 * M)
    (hij : i ≠ j) :
    ipu i j * ipw M i j * (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s) = 0 := by
  have key : ipu i j = 0 ∨ ipw M i j = 0 ∨
      (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s) = 0 := by
    rcases decomp M i hi with hio | ⟨mm, tt, hmm, htt, rfl⟩
    · rcases decomp M j hj with hjo | ⟨mm', tt', hmm', htt', rfl⟩
      · exact case_OO M i j hM hio hjo hij
      · exact (case_ON M i mm' tt' hM hio hmm' htt').imp_right id |>.imp_left id |> Or.inr
    · rcases decomp M j hj with hjo | ⟨mm', tt', hmm', htt', rfl⟩
      · have := case_ON M j mm tt hM hjo hmm htt
        refine Or.inr ?_
        rcases this with h | h
        · exact Or.inl (by rw [ipw_symm]; exact h)
        · exact Or.inr (by rw [ipz_symm]; exact h)
      · refine case_NN M mm tt mm' tt' hmm hmm' htt htt' ?_
        rintro ⟨rfl, rfl⟩
        exact hij rfl
  rcases key with h | h | h
  · rw [h]; ring
  · rw [h]; ring
  · rw [h]; ring


-- ### nonzero factors

lemma UI_nz (i : ℕ) : UI i 0 ≠ 0 ∨ UI i 1 ≠ 0 := by
  unfold UI
  by_cases h : clsI i % 2 = 0
  · left; simp [h]
  · right; simp [h]

lemma WI_nz (M i : ℕ) : WI M i 0 ≠ 0 ∨ WI M i 1 ≠ 0 := by
  unfold WI
  by_cases h : wsI i = 0
  · left; simp [h]
  · right; simp [h]

lemma Zb_nz : ∀ i ∈ Finset.range 14, ∃ s ∈ Finset.range 11, Zb i s ≠ 0 := by decide

lemma dual_diag (tt : ℕ) (htt : tt < 4) : dual tt tt = 1 := by
  interval_cases tt <;> norm_num [dual, sA, sB, sC, sD]

lemma ZG_nz (M i : ℕ) (hi : i < 14 + 4 * M) : ∃ s, s < 11 + 4 * M ∧ ZG i s ≠ 0 := by
  rcases decomp M i hi with hio | ⟨mm, tt, hmm, htt, rfl⟩
  · obtain ⟨s, hs, hne⟩ := Zb_nz i (Finset.mem_range.mpr hio)
    exact ⟨s, by have := Finset.mem_range.mp hs; omega, by
      rw [ZG_base i s (Finset.mem_range.mp hs)]; exact hne⟩
  · refine ⟨11 + 4 * mm + tt, by omega, ?_⟩
    rw [ZG_win' _ mm tt htt, EW_new mm tt mm tt htt]
    simp [dual_diag tt htt]


def Y3 : ℕ → ℕ → ℤ := fun r i =>
  ((([[185, 1440, 60, 352, 315, 1010, -145, 1016, -1705, -10545, -3060, -2020, -18180, 40905],
     [350, 1455, -255, 322, -960, 0, -15, 126, 6110, 37620, -2145, 3030, 40905, 19695],
     [-610, -285, -75, -743, 1500, -1010, 55, -1169, -9610, -59160, 795, 2020, 22725, -13635]] : List (List ℤ)).getD r []).getD i 0)

/-- Column `i` of the relation matrix. For a new state the column is affine-linear in the
block index, which is what makes every unextendibility condition a polynomial in it. -/
def YI (r i : ℕ) : ℤ :=
  if i < 14 then Y3 r i
  else
    let mm := (i - 14) / 4
    let tt := (i - 14) % 4
    let t : ℤ := (mm : ℤ) + 1
    if tt = 0 then Y3 r 10 + t * (2 * Y3 r 2 - Y3 r 1)
    else if tt = 1 then -Y3 r 12 - 2 * Y3 r 10 + (2 * t - 1) * Y3 r 2
    else if tt = 2 then Y3 r 12 + t * (2 * Y3 r 1 - 6 * Y3 r 2)
    else -2 * Y3 r 12 - 6 * Y3 r 10 + (2 * t - 1) * Y3 r 1

lemma YI_old (r i : ℕ) (h : i < 14) : YI r i = Y3 r i := by simp [YI, h]

lemma YI_new (r mm tt : ℕ) (htt : tt < 4) :
    YI r (14 + 4 * mm + tt) =
      (if tt = 0 then Y3 r 10 + ((mm : ℤ) + 1) * (2 * Y3 r 2 - Y3 r 1)
       else if tt = 1 then -Y3 r 12 - 2 * Y3 r 10 + (2 * ((mm : ℤ) + 1) - 1) * Y3 r 2
       else if tt = 2 then Y3 r 12 + ((mm : ℤ) + 1) * (2 * Y3 r 1 - 6 * Y3 r 2)
       else -2 * Y3 r 12 - 6 * Y3 r 10 + (2 * ((mm : ℤ) + 1) - 1) * Y3 r 1) := by
  have h1 : ¬ (14 + 4 * mm + tt < 14) := by omega
  have h2 : (14 + 4 * mm + tt - 14) = 4 * mm + tt := by omega
  have h3 : (4 * mm + tt) / 4 = mm := by omega
  have h4 : (4 * mm + tt) % 4 = tt := by omega
  simp [YI, h1, h2, h3, h4]

lemma sum_blocks14 (g : ℕ → ℤ) (M : ℕ) :
    ∑ i ∈ Finset.range (14 + 4 * M), g i
      = (∑ i ∈ Finset.range 14, g i)
        + ∑ m ∈ Finset.range M, (g (14+4*m) + g (14+4*m+1) + g (14+4*m+2) + g (14+4*m+3)) := by
  rw [Finset.sum_range_add]
  congr 1
  have := sum_blocks (fun s => g (14 + s)) M
  simpa [Nat.add_assoc] using this

lemma YZ_base_dec : ∀ r ∈ Finset.range 3, ∀ s ∈ Finset.range 11,
    (∑ i ∈ Finset.range 14, Y3 r i * Zb i s) = 0 := by decide


lemma EW_newA (mm m t : ℕ) :
    EW (14 + 4 * mm) m t = (if mm = m then dual 0 t else if m = mm + 1 then eD t else 0) := by
  have h : (14 : ℕ) + 4 * mm = 14 + 4 * mm + 0 := rfl
  rw [h, EW_new mm 0 m t (by norm_num)]
  simp

lemma YI_newA (r mm : ℕ) :
    YI r (14 + 4 * mm) = Y3 r 10 + ((mm : ℤ) + 1) * (2 * Y3 r 2 - Y3 r 1) := by
  have h : (14 : ℕ) + 4 * mm = 14 + 4 * mm + 0 := rfl
  rw [h, YI_new r mm 0 (by norm_num)]
  simp

lemma YZ_win_first (r m0 t0 : ℕ) :
    (∑ i ∈ Finset.range 14, YI r i * EW i m0 t0)
      = Y3 r 1 * eA t0 + Y3 r 2 * eC t0
        + (if m0 = 0 then Y3 r 10 * eD t0 + Y3 r 12 * eB t0 else 0) := by
  by_cases hm : m0 = 0 <;>
    simp [Finset.sum_range_succ, EW, YI, hm] <;> ring

lemma YZ_win_block (r m m0 t0 : ℕ) :
    (YI r (14 + 4 * m) * EW (14 + 4 * m) m0 t0
      + YI r (14 + 4 * m + 1) * EW (14 + 4 * m + 1) m0 t0
      + YI r (14 + 4 * m + 2) * EW (14 + 4 * m + 2) m0 t0
      + YI r (14 + 4 * m + 3) * EW (14 + 4 * m + 3) m0 t0)
      = (if m = m0 then
            YI r (14 + 4 * m) * dual 0 t0 + YI r (14 + 4 * m + 1) * dual 1 t0
              + YI r (14 + 4 * m + 2) * dual 2 t0 + YI r (14 + 4 * m + 3) * dual 3 t0
         else if m0 = m + 1 then
            YI r (14 + 4 * m) * eD t0 + YI r (14 + 4 * m + 2) * eB t0
         else 0) := by
  rw [EW_newA m m0 t0, EW_new m 1 m0 t0 (by norm_num), EW_new m 2 m0 t0 (by norm_num),
      EW_new m 3 m0 t0 (by norm_num)]
  by_cases h1 : m = m0
  · simp [h1]
  · by_cases h2 : m0 = m + 1 <;> simp [h1, h2] <;> ring


lemma key_identity (r t0 : ℕ) (hr : r < 3) (ht0 : t0 < 4) (x : ℤ) :
    Y3 r 1 * eA t0 + Y3 r 2 * eC t0
    + ((Y3 r 10 + x * (2 * Y3 r 2 - Y3 r 1)) * eD t0
        + (Y3 r 12 + x * (2 * Y3 r 1 - 6 * Y3 r 2)) * eB t0)
    + ((Y3 r 10 + (x + 1) * (2 * Y3 r 2 - Y3 r 1)) * dual 0 t0
        + (-Y3 r 12 - 2 * Y3 r 10 + (2 * (x + 1) - 1) * Y3 r 2) * dual 1 t0
        + (Y3 r 12 + (x + 1) * (2 * Y3 r 1 - 6 * Y3 r 2)) * dual 2 t0
        + (-2 * Y3 r 12 - 6 * Y3 r 10 + (2 * (x + 1) - 1) * Y3 r 1) * dual 3 t0) = 0 := by
  interval_cases r <;> interval_cases t0 <;>
    norm_num [Y3, eA, eB, eC, eD, dual, sA, sB, sC, sD] <;> ring

lemma sum_sel (M m0 : ℕ) (D E : ℕ → ℤ) (hm0 : m0 < M) :
    (∑ m ∈ Finset.range M, (if m = m0 then D m else if m0 = m + 1 then E m else 0))
      = D m0 + (if m0 = 0 then 0 else E (m0 - 1)) := by
  by_cases h0 : m0 = 0
  · subst h0
    rw [sum_one (fun m => if m = 0 then D m else if (0:ℕ) = m + 1 then E m else 0) 0 M hm0
      (fun m hm => by simp [hm, (by omega : ¬((0:ℕ) = m + 1))])]
    simp
  · have h1 : 1 ≤ m0 := by omega
    rw [sum_two (fun m => if m = m0 then D m else if m0 = m + 1 then E m else 0) (m0 - 1) M
      (by omega) (fun m ha hb => by
        have e2 : ¬ (m0 = m + 1) := by omega
        have e4 : ¬ (m = m0) := by omega
        simp [e4, e2])]
    have e1 : ¬ (m0 - 1 = m0) := by omega
    have e2 : m0 = m0 - 1 + 1 := by omega
    have e3 : m0 - 1 + 1 = m0 := by omega
    simp only [if_neg e1, e3]
    simp [h0]
    ring

lemma YZ_win (M r m0 t0 : ℕ) (hr : r < 3) (hm0 : m0 < M) (ht0 : t0 < 4) :
    (∑ i ∈ Finset.range (14 + 4 * M), YI r i * EW i m0 t0) = 0 := by
  rw [sum_blocks14, YZ_win_first]
  rw [Finset.sum_congr rfl (fun m _ => YZ_win_block r m m0 t0)]
  rw [sum_sel M m0
    (fun m => YI r (14 + 4 * m) * dual 0 t0 + YI r (14 + 4 * m + 1) * dual 1 t0
      + YI r (14 + 4 * m + 2) * dual 2 t0 + YI r (14 + 4 * m + 3) * dual 3 t0)
    (fun m => YI r (14 + 4 * m) * eD t0 + YI r (14 + 4 * m + 2) * eB t0) hm0]
  rw [YI_newA r m0, YI_new r m0 1 (by norm_num), YI_new r m0 2 (by norm_num),
      YI_new r m0 3 (by norm_num)]
  simp only [if_pos rfl, if_neg (by norm_num : ¬ (1 = 0)), if_neg (by norm_num : ¬ (2 = 0)),
    if_neg (by norm_num : ¬ (3 = 0)), if_neg (by norm_num : ¬ (2 = 1)),
    if_neg (by norm_num : ¬ (3 = 1)), if_neg (by norm_num : ¬ (3 = 2))]
  by_cases h0 : m0 = 0
  · subst h0
    simp only [if_pos rfl]
    have := key_identity r t0 hr ht0 0
    push_cast
    push_cast at this
    linear_combination this
  · have h1 : 1 ≤ m0 := by omega
    simp only [if_neg h0]
    rw [YI_newA r (m0 - 1), YI_new r (m0 - 1) 2 (by norm_num)]
    simp only [if_pos rfl, if_neg (by norm_num : ¬ (2 = 0)), if_neg (by norm_num : ¬ (2 = 1))]
    have hx : ((m0 - 1 : ℕ) : ℤ) + 1 = (m0 : ℤ) := by
      have : ((m0 - 1 : ℕ) : ℤ) = (m0 : ℤ) - 1 := by
        push_cast [Nat.cast_sub h1]; ring
      rw [this]; ring
    have := key_identity r t0 hr ht0 (m0 : ℤ)
    rw [hx]
    push_cast
    push_cast at this
    linear_combination this


lemma decompS (M s : ℕ) (h : ¬ (s < 11)) (hs : s < 11 + 4 * M) :
    ∃ m0 t0, m0 < M ∧ t0 < 4 ∧ s = 11 + 4 * m0 + t0 :=
  ⟨(s - 11) / 4, (s - 11) % 4, by omega, by omega, by omega⟩

theorem YZ (M r s : ℕ) (hr : r < 3) (hs : s < 11 + 4 * M) :
    (∑ i ∈ Finset.range (14 + 4 * M), YI r i * ZG i s) = 0 := by
  by_cases h : s < 11
  · rw [sum_blocks14]
    have h1 : (∑ i ∈ Finset.range 14, YI r i * ZG i s) = 0 := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [YI_old r i (Finset.mem_range.mp hi), ZG_base i s h])]
      exact YZ_base_dec r (Finset.mem_range.mpr hr) s (Finset.mem_range.mpr h)
    have h2 : ∀ m, (YI r (14 + 4 * m) * ZG (14 + 4 * m) s
        + YI r (14 + 4 * m + 1) * ZG (14 + 4 * m + 1) s
        + YI r (14 + 4 * m + 2) * ZG (14 + 4 * m + 2) s
        + YI r (14 + 4 * m + 3) * ZG (14 + 4 * m + 3) s) = 0 := by
      intro m
      rw [ZG_base _ s h, ZG_base _ s h, ZG_base _ s h, ZG_base _ s h,
        Zb_big (14 + 4 * m) s (by omega), Zb_big (14 + 4 * m + 1) s (by omega),
        Zb_big (14 + 4 * m + 2) s (by omega), Zb_big (14 + 4 * m + 3) s (by omega)]
      ring
    rw [h1, sum_all_zero _ M h2]
    ring
  · obtain ⟨m0, t0, hm0, ht0, rfl⟩ := decompS M s h hs
    rw [Finset.sum_congr rfl (fun i _ => by rw [ZG_win' i m0 t0 ht0])]
    exact YZ_win M r m0 t0 hr hm0 ht0


-- ### injectivity of the third-factor matrix

lemma sum_blocksC {A : Type*} [AddCommMonoid A] (g : ℕ → A) : ∀ M : ℕ,
    ∑ s ∈ Finset.range (4 * M), g s
      = ∑ m ∈ Finset.range M, (g (4*m) + g (4*m+1) + g (4*m+2) + g (4*m+3)) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    have h4 : 4 * (M + 1) = 4 * M + 4 := by ring
    rw [h4, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    simp [Finset.sum_range_succ]

lemma split11C {A : Type*} [AddCommMonoid A] (g : ℕ → A) (M : ℕ) :
    ∑ s ∈ Finset.range (11 + 4 * M), g s
      = (∑ s ∈ Finset.range 11, g s)
        + ∑ m ∈ Finset.range M, (g (11+4*m) + g (11+4*m+1) + g (11+4*m+2) + g (11+4*m+3)) := by
  rw [Finset.sum_range_add]
  congr 1
  have := sum_blocksC (fun s => g (11 + s)) M
  simpa [Nat.add_assoc] using this

lemma sum_allC {A : Type*} [AddCommMonoid A] (f : ℕ → A) (M : ℕ) (h : ∀ m, f m = 0) :
    ∑ m ∈ Finset.range M, f m = 0 := Finset.sum_eq_zero fun m _ => h m

lemma sum_oneC {A : Type*} [AddCommMonoid A] (f : ℕ → A) (a M : ℕ) (ha : a < M)
    (h : ∀ m, m ≠ a → f m = 0) : ∑ m ∈ Finset.range M, f m = f a := by
  rw [Finset.sum_eq_single a]
  · intro b _ hb; exact h b hb
  · intro hb; exact absurd (Finset.mem_range.mpr ha) hb

lemma sum_twoC {A : Type*} [AddCommMonoid A] (f : ℕ → A) (a M : ℕ) (ha : a + 1 < M)
    (h : ∀ m, m ≠ a → m ≠ a + 1 → f m = 0) :
    ∑ m ∈ Finset.range M, f m = f a + f (a + 1) := by
  have hsub : ({a, a + 1} : Finset ℕ) ⊆ Finset.range M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun x _ hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact h x hx.1 hx.2)]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]


lemma sum_selC {A : Type*} [AddCommMonoid A] (M m0 : ℕ) (D E : ℕ → A) (hm0 : m0 < M) :
    (∑ m ∈ Finset.range M, (if m = m0 then D m else if m0 = m + 1 then E m else 0))
      = D m0 + (if m0 = 0 then 0 else E (m0 - 1)) := by
  by_cases h0 : m0 = 0
  · subst h0
    rw [sum_oneC (fun m => if m = 0 then D m else if (0:ℕ) = m + 1 then E m else 0) 0 M hm0
      (fun m hm => by simp [hm, (by omega : ¬((0:ℕ) = m + 1))])]
    simp
  · have h1 : 1 ≤ m0 := by omega
    rw [sum_twoC (fun m => if m = m0 then D m else if m0 = m + 1 then E m else 0) (m0 - 1) M
      (by omega) (fun m ha hb => by
        have e2 : ¬ (m0 = m + 1) := by omega
        have e4 : ¬ (m = m0) := by omega
        simp [e4, e2])]
    have e1 : ¬ (m0 - 1 = m0) := by omega
    have e3 : m0 - 1 + 1 = m0 := by omega
    simp only [if_neg e1, e3]
    simp [h0, add_comm]



lemma sum_oneC' {A : Type*} [AddCommMonoid A] (f : ℕ → A) (a M : ℕ) (ha : a < M)
    (h : ∀ m, m < M → m ≠ a → f m = 0) : ∑ m ∈ Finset.range M, f m = f a := by
  rw [Finset.sum_eq_single a]
  · intro b hb hba; exact h b (Finset.mem_range.mp hb) hba
  · intro hb; exact absurd (Finset.mem_range.mpr ha) hb

lemma sum_sel2C {A : Type*} [AddCommMonoid A] (M a : ℕ) (D E : ℕ → A) (ha : a < M) :
    (∑ m ∈ Finset.range M, (if m = a then D m else if m = a + 1 then E m else 0))
      = D a + (if a + 1 < M then E (a + 1) else 0) := by
  by_cases h : a + 1 < M
  · rw [sum_twoC (fun m => if m = a then D m else if m = a + 1 then E m else 0) a M h
      (fun m h1 h2 => by simp [h1, h2])]
    simp [h, (by omega : ¬ (a + 1 = a))]
  · rw [sum_oneC' (fun m => if m = a then D m else if m = a + 1 then E m else 0) a M ha
      (fun m hmM hm => by
        have h2 : ¬ (m = a + 1) := by omega
        simp [hm, h2])]
    simp [h]

/-- The window pattern a new state contributes to the window one step to its right. -/
def XT (tt t : ℕ) : ℤ := if tt = 0 then eD t else if tt = 2 then eB t else 0

lemma newSum (M m tt : ℕ) (htt : tt < 4) (hm : m < M) (c : ℕ → ℂ) :
    (∑ s ∈ Finset.range (11 + 4 * M), ((ZG (14 + 4*m + tt) s : ℤ) : ℂ) * c s)
      = (((dual tt 0 : ℤ) : ℂ) * c (11+4*m) + ((dual tt 1 : ℤ) : ℂ) * c (11+4*m+1)
          + ((dual tt 2 : ℤ) : ℂ) * c (11+4*m+2) + ((dual tt 3 : ℤ) : ℂ) * c (11+4*m+3))
        + (if m + 1 < M then
            (((XT tt 0 : ℤ) : ℂ) * c (11+4*(m+1)) + ((XT tt 1 : ℤ) : ℂ) * c (11+4*(m+1)+1)
              + ((XT tt 2 : ℤ) : ℂ) * c (11+4*(m+1)+2) + ((XT tt 3 : ℤ) : ℂ) * c (11+4*(m+1)+3))
           else 0) := by
  rw [split11C (fun s => ((ZG (14 + 4*m + tt) s : ℤ) : ℂ) * c s) M]
  have hbase : (∑ s ∈ Finset.range 11, ((ZG (14 + 4*m + tt) s : ℤ) : ℂ) * c s) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [ZG_base _ s (Finset.mem_range.mp hs), Zb_big _ s (by omega)]
    simp
  rw [hbase, zero_add]
  have hterm : ∀ m', ((((ZG (14+4*m+tt) (11+4*m') : ℤ) : ℂ) * c (11+4*m')
      + ((ZG (14+4*m+tt) (11+4*m'+1) : ℤ) : ℂ) * c (11+4*m'+1)
      + ((ZG (14+4*m+tt) (11+4*m'+2) : ℤ) : ℂ) * c (11+4*m'+2)
      + ((ZG (14+4*m+tt) (11+4*m'+3) : ℤ) : ℂ) * c (11+4*m'+3)))
      = (if m' = m then
          ((dual tt 0 : ℤ) : ℂ) * c (11+4*m') + ((dual tt 1 : ℤ) : ℂ) * c (11+4*m'+1)
            + ((dual tt 2 : ℤ) : ℂ) * c (11+4*m'+2) + ((dual tt 3 : ℤ) : ℂ) * c (11+4*m'+3)
         else if m' = m + 1 then
          ((XT tt 0 : ℤ) : ℂ) * c (11+4*m') + ((XT tt 1 : ℤ) : ℂ) * c (11+4*m'+1)
            + ((XT tt 2 : ℤ) : ℂ) * c (11+4*m'+2) + ((XT tt 3 : ℤ) : ℂ) * c (11+4*m'+3)
         else 0) := by
    intro m'
    have e0 : (11:ℕ) + 4*m' = 11 + 4*m' + 0 := rfl
    rw [e0]
    rw [ZG_win' _ m' 0 (by norm_num), ZG_win' _ m' 1 (by norm_num),
        ZG_win' _ m' 2 (by norm_num), ZG_win' _ m' 3 (by norm_num),
        EW_new m tt m' 0 htt, EW_new m tt m' 1 htt, EW_new m tt m' 2 htt, EW_new m tt m' 3 htt]
    by_cases h1 : m' = m
    · simp [h1]
    · by_cases h2 : m' = m + 1 <;> simp [h1, h2, XT, Ne.symm h1] <;> ring
  rw [Finset.sum_congr rfl (fun m' _ => hterm m')]
  rw [sum_sel2C M m
    (fun m' => ((dual tt 0 : ℤ) : ℂ) * c (11+4*m') + ((dual tt 1 : ℤ) : ℂ) * c (11+4*m'+1)
      + ((dual tt 2 : ℤ) : ℂ) * c (11+4*m'+2) + ((dual tt 3 : ℤ) : ℂ) * c (11+4*m'+3))
    (fun m' => ((XT tt 0 : ℤ) : ℂ) * c (11+4*m') + ((XT tt 1 : ℤ) : ℂ) * c (11+4*m'+1)
      + ((XT tt 2 : ℤ) : ℂ) * c (11+4*m'+2) + ((XT tt 3 : ℤ) : ℂ) * c (11+4*m'+3)) hm]


lemma injWindows (M : ℕ) (c : ℕ → ℂ)
    (h : ∀ m tt, m < M → tt < 4 →
      (∑ s ∈ Finset.range (11 + 4 * M), ((ZG (14 + 4*m + tt) s : ℤ) : ℂ) * c s) = 0) :
    ∀ m, m < M →
      (c (11+4*m) = 0 ∧ c (11+4*m+1) = 0 ∧ c (11+4*m+2) = 0 ∧ c (11+4*m+3) = 0) := by
  have step : ∀ m, m < M →
      (if m + 1 < M then
        (c (11+4*(m+1)) = 0 ∧ c (11+4*(m+1)+1) = 0 ∧ c (11+4*(m+1)+2) = 0
          ∧ c (11+4*(m+1)+3) = 0) else True) →
      (c (11+4*m) = 0 ∧ c (11+4*m+1) = 0 ∧ c (11+4*m+2) = 0 ∧ c (11+4*m+3) = 0) := by
    intro m hm hnext
    have e3 := h m 3 hm (by norm_num)
    rw [newSum M m 3 (by norm_num) hm c] at e3
    norm_num [dual, sA, sB, sC, sD, XT, eD, eB] at e3
    have e1 := h m 1 hm (by norm_num)
    rw [newSum M m 1 (by norm_num) hm c] at e1
    norm_num [dual, sA, sB, sC, sD, XT, eD, eB] at e1
    have e2 := h m 2 hm (by norm_num)
    rw [newSum M m 2 (by norm_num) hm c] at e2
    norm_num [dual, sA, sB, sC, sD, XT, eD, eB] at e2
    have e0 := h m 0 hm (by norm_num)
    rw [newSum M m 0 (by norm_num) hm c] at e0
    norm_num [dual, sA, sB, sC, sD, XT, eD, eB] at e0
    by_cases hnx : m + 1 < M
    · rw [if_pos hnx] at hnext
      obtain ⟨n0, n1, n2, n3⟩ := hnext
      rw [if_pos hnx] at e2 e0
      rw [n1] at e2
      have h2 : c (11+4*m+2) = 0 := by linear_combination e2
      have h1 : c (11+4*m+1) = 0 := by linear_combination e1 - h2 + 2 * e3
      rw [n0, n1, n3] at e0
      have h0 : c (11+4*m) = 0 := by linear_combination e0 - 2 * h2 - e3
      exact ⟨h0, h1, h2, e3⟩
    · rw [if_neg hnx] at e2 e0
      have h2 : c (11+4*m+2) = 0 := by linear_combination e2
      have h1 : c (11+4*m+1) = 0 := by linear_combination e1 - h2 + 2 * e3
      have h0 : c (11+4*m) = 0 := by linear_combination e0 - 2 * h2 - e3
      exact ⟨h0, h1, h2, e3⟩
  have key : ∀ j m, m < M → M ≤ m + j + 1 →
      (c (11+4*m) = 0 ∧ c (11+4*m+1) = 0 ∧ c (11+4*m+2) = 0 ∧ c (11+4*m+3) = 0) := by
    intro j
    induction j with
    | zero =>
      intro m hm hMj
      refine step m hm ?_
      rw [if_neg (by omega)]
      trivial
    | succ j ih =>
      intro m hm hMj
      by_cases hc : M ≤ m + j + 1
      · exact ih m hm hc
      · refine step m hm ?_
        have hm1 : m + 1 < M := by omega
        rw [if_pos hm1]
        exact ih (m + 1) hm1 (by omega)
  intro m hm
  exact key M m hm (by omega)


def L3 : ℕ → ℕ → ℤ := fun t i =>
  ((([[0, 18, 0, 0, 0, 0, 0, 0, 0, 0, -18, 0, 36, 216],
     [0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, -6, -72, 12],
     [0, -36, 0, 0, -18, -12, 3, -12, 108, 666, 72, 18, 72, -903],
     [0, -12, 0, 0, -15, -5, 1, -2, 90, 555, 24, 7, 36, -303],
     [0, -12, 0, 0, 3, -5, 1, -2, -18, -111, 24, 7, 36, -303],
     [0, 0, 0, 0, 0, 0, 0, 0, -18, -108, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, -36, -216],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 216, -36],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -18]] : List (List ℤ)).getD t []).getD i 0)

lemma LZ_dec : ∀ t ∈ Finset.range 11, ∀ s ∈ Finset.range 11,
    (∑ i ∈ Finset.range 14, L3 t i * Zb i s) = (if t = s then (18 : ℤ) else 0) := by decide

lemma injBase (M : ℕ) (c : ℕ → ℂ)
    (hw : ∀ m, m < M →
      (c (11+4*m) = 0 ∧ c (11+4*m+1) = 0 ∧ c (11+4*m+2) = 0 ∧ c (11+4*m+3) = 0))
    (h : ∀ i, i < 14 → (∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c s) = 0) :
    ∀ t, t < 11 → c t = 0 := by
  have hb : ∀ i, i < 14 → (∑ s ∈ Finset.range 11, ((Zb i s : ℤ) : ℂ) * c s) = 0 := by
    intro i hi
    have hh := h i hi
    rw [split11C (fun s => ((ZG i s : ℤ) : ℂ) * c s) M] at hh
    have hz : (∑ m ∈ Finset.range M,
        (((ZG i (11+4*m) : ℤ) : ℂ) * c (11+4*m) + ((ZG i (11+4*m+1) : ℤ) : ℂ) * c (11+4*m+1)
          + ((ZG i (11+4*m+2) : ℤ) : ℂ) * c (11+4*m+2)
          + ((ZG i (11+4*m+3) : ℤ) : ℂ) * c (11+4*m+3))) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      obtain ⟨g0, g1, g2, g3⟩ := hw m (Finset.mem_range.mp hm)
      rw [g0, g1, g2, g3]
      ring
    rw [hz, add_zero] at hh
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [ZG_base i s (Finset.mem_range.mp hs)])] at hh
    exact hh
  intro t ht
  have key : (∑ i ∈ Finset.range 14,
      ((L3 t i : ℤ) : ℂ) * (∑ s ∈ Finset.range 11, ((Zb i s : ℤ) : ℂ) * c s))
      = ((18 : ℤ) : ℂ) * c t := by
    have hswap : (∑ i ∈ Finset.range 14,
        ((L3 t i : ℤ) : ℂ) * ∑ s ∈ Finset.range 11, ((Zb i s : ℤ) : ℂ) * c s)
        = ∑ s ∈ Finset.range 11,
            (∑ i ∈ Finset.range 14, ((L3 t i : ℤ) : ℂ) * ((Zb i s : ℤ) : ℂ)) * c s := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hswap]
    rw [Finset.sum_congr rfl (fun s hs => by
      have hs' := Finset.mem_range.mp hs
      have hc : (∑ i ∈ Finset.range 14, ((L3 t i : ℤ) : ℂ) * ((Zb i s : ℤ) : ℂ))
          = ((∑ i ∈ Finset.range 14, L3 t i * Zb i s : ℤ) : ℂ) := by push_cast; ring
      rw [hc, LZ_dec t (Finset.mem_range.mpr ht) s (Finset.mem_range.mpr hs')])]
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hst; simp [Ne.symm hst]
    · intro hns; exact absurd (Finset.mem_range.mpr ht) hns
  have hzero : ((18 : ℤ) : ℂ) * c t = 0 := by
    rw [← key]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hb i (Finset.mem_range.mp hi), mul_zero]
  have h18 : ((18 : ℤ) : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hzero).resolve_left h18

theorem injAll (M : ℕ) (c : ℕ → ℂ)
    (h : ∀ i, i < 14 + 4 * M → (∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c s) = 0) :
    ∀ s, s < 11 + 4 * M → c s = 0 := by
  have hw := injWindows M c (fun m tt hm htt => h (14 + 4*m + tt) (by omega))
  have hbase := injBase M c hw (fun i hi => h i (by omega))
  intro s hs
  by_cases h11 : s < 11
  · exact hbase s h11
  · obtain ⟨m0, t0, hm0, ht0, rfl⟩ := decompS M s h11 hs
    obtain ⟨g0, g1, g2, g3⟩ := hw m0 hm0
    interval_cases t0
    · simpa using g0
    · simpa using g1
    · simpa using g2
    · simpa using g3


-- ### the 3 x 3 determinants of relation columns

def dt (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℤ) : ℤ :=
  a0 * (b1 * c2 - b2 * c1) - b0 * (a1 * c2 - a2 * c1) + c0 * (a1 * b2 - a2 * b1)

def D3g (p q j : ℕ) : ℤ :=
  dt (YI 0 p) (YI 1 p) (YI 2 p) (YI 0 q) (YI 1 q) (YI 2 q) (YI 0 j) (YI 1 j) (YI 2 j)

lemma dAB_form (m : ℕ) (c0 c1 c2 : ℤ) :
    dt (YI 0 (14 + 4*m)) (YI 1 (14 + 4*m)) (YI 2 (14 + 4*m))
       (YI 0 (14 + 4*m + 1)) (YI 1 (14 + 4*m + 1)) (YI 2 (14 + 4*m + 1)) c0 c1 c2
    = 181800 * ((2*c0 - c1 + 5*c2) * (((m : ℤ) + 1))^2
        + (293*c0 - 160*c1 + 536*c2) * ((m : ℤ) + 1)
        + (445*c0 - 302*c1 + 898*c2)) := by
  rw [YI_newA, YI_newA, YI_newA, YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num),
      YI_new 2 m 1 (by norm_num)]
  norm_num [dt, Y3]
  ring

lemma dCD_form (m : ℕ) (c0 c1 c2 : ℤ) :
    dt (YI 0 (14 + 4*m + 2)) (YI 1 (14 + 4*m + 2)) (YI 2 (14 + 4*m + 2))
       (YI 0 (14 + 4*m + 3)) (YI 1 (14 + 4*m + 3)) (YI 2 (14 + 4*m + 3)) c0 c1 c2
    = -272700 * (4*(2*c0 - c1 + 5*c2) * (((m : ℤ) + 1))^2
        + 4*(293*c0 - 160*c1 + 536*c2) * ((m : ℤ) + 1)
        + (1624*c0 - 1111*c1 + 3299*c2)) := by
  rw [YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num),
      YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
  norm_num [dt, Y3]
  ring


lemma dAB_ne_b0 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 0 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 0 (by norm_num), YI_old 1 0 (by norm_num), YI_old 2 0 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b1 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 1 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 1 (by norm_num), YI_old 1 1 (by norm_num), YI_old 2 1 (by norm_num), dAB_form]
  norm_num [Y3]
  omega

lemma dAB_ne_b2 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 2 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 2 (by norm_num), YI_old 1 2 (by norm_num), YI_old 2 2 (by norm_num), dAB_form]
  norm_num [Y3]
  omega

lemma dAB_ne_b3 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 3 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 3 (by norm_num), YI_old 1 3 (by norm_num), YI_old 2 3 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b4 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 4 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 4 (by norm_num), YI_old 1 4 (by norm_num), YI_old 2 4 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b5 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 5 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 5 (by norm_num), YI_old 1 5 (by norm_num), YI_old 2 5 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b6 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 6 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 6 (by norm_num), YI_old 1 6 (by norm_num), YI_old 2 6 (by norm_num), dAB_form]
  norm_num [Y3]
  omega

lemma dAB_ne_b7 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 7 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 7 (by norm_num), YI_old 1 7 (by norm_num), YI_old 2 7 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b8 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 8 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 8 (by norm_num), YI_old 1 8 (by norm_num), YI_old 2 8 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b9 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 9 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 9 (by norm_num), YI_old 1 9 (by norm_num), YI_old 2 9 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b10 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 10 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 10 (by norm_num), YI_old 1 10 (by norm_num), YI_old 2 10 (by norm_num), dAB_form]
  norm_num [Y3]
  omega

lemma dAB_ne_b11 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 11 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 11 (by norm_num), YI_old 1 11 (by norm_num), YI_old 2 11 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b12 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 12 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 12 (by norm_num), YI_old 1 12 (by norm_num), YI_old 2 12 (by norm_num), dAB_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dAB_ne_b13 (m : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) 13 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 13 (by norm_num), YI_old 1 13 (by norm_num), YI_old 2 13 (by norm_num), dAB_form]
  norm_num [Y3]
  intro hc
  by_cases hb : ((m : ℤ) + 1) ≤ 251
  · nlinarith [hX, hb, mul_nonneg (by linarith : (0:ℤ) ≤ ((m:ℤ)+1) - 1) (by linarith : (0:ℤ) ≤ 251 - ((m:ℤ)+1))]
  · push_neg at hb
    nlinarith [hX, hb, mul_nonneg (by linarith : (0:ℤ) ≤ ((m:ℤ)+1) - 252) (by linarith : (0:ℤ) ≤ ((m:ℤ)+1))]

lemma dCD_ne_b0 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 0 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 0 (by norm_num), YI_old 1 0 (by norm_num), YI_old 2 0 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b1 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 1 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 1 (by norm_num), YI_old 1 1 (by norm_num), YI_old 2 1 (by norm_num), dCD_form]
  norm_num [Y3]
  omega

lemma dCD_ne_b2 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 2 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 2 (by norm_num), YI_old 1 2 (by norm_num), YI_old 2 2 (by norm_num), dCD_form]
  norm_num [Y3]
  omega

lemma dCD_ne_b3 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 3 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 3 (by norm_num), YI_old 1 3 (by norm_num), YI_old 2 3 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b4 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 4 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 4 (by norm_num), YI_old 1 4 (by norm_num), YI_old 2 4 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b5 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 5 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 5 (by norm_num), YI_old 1 5 (by norm_num), YI_old 2 5 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b6 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 6 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 6 (by norm_num), YI_old 1 6 (by norm_num), YI_old 2 6 (by norm_num), dCD_form]
  norm_num [Y3]
  omega

lemma dCD_ne_b7 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 7 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 7 (by norm_num), YI_old 1 7 (by norm_num), YI_old 2 7 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b8 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 8 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 8 (by norm_num), YI_old 1 8 (by norm_num), YI_old 2 8 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b9 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 9 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 9 (by norm_num), YI_old 1 9 (by norm_num), YI_old 2 9 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b10 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 10 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 10 (by norm_num), YI_old 1 10 (by norm_num), YI_old 2 10 (by norm_num), dCD_form]
  norm_num [Y3]
  omega

lemma dCD_ne_b11 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 11 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 11 (by norm_num), YI_old 1 11 (by norm_num), YI_old 2 11 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b12 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 12 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 12 (by norm_num), YI_old 1 12 (by norm_num), YI_old 2 12 (by norm_num), dCD_form]
  norm_num [Y3]
  nlinarith [hX, hX2]

lemma dCD_ne_b13 (m : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) 13 ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hX2 : (1:ℤ) ≤ ((m : ℤ) + 1)^2 := by nlinarith [hX]
  rw [D3g, YI_old 0 13 (by norm_num), YI_old 1 13 (by norm_num), YI_old 2 13 (by norm_num), dCD_form]
  norm_num [Y3]
  intro hc
  by_cases hb : ((m : ℤ) + 1) ≤ 251
  · nlinarith [hX, hb, mul_nonneg (by linarith : (0:ℤ) ≤ ((m:ℤ)+1) - 1) (by linarith : (0:ℤ) ≤ 251 - ((m:ℤ)+1))]
  · push_neg at hb
    nlinarith [hX, hb, mul_nonneg (by linarith : (0:ℤ) ≤ ((m:ℤ)+1) - 252) (by linarith : (0:ℤ) ≤ ((m:ℤ)+1))]



def M2 (r1 r2 p j : ℕ) : ℤ := YI r1 p * YI r2 j - YI r2 p * YI r1 j

lemma dB_0_1_0 (m : ℕ) : D3g 0 1 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 0 1 (14 + 4*m + 0) = (550854000 : ℤ) * ((m : ℤ) + 1) + (-826281000) := by
    rw [D3g, YI_old 0 0 (by norm_num), YI_old 1 0 (by norm_num), YI_old 2 0 (by norm_num),
        YI_old 0 1 (by norm_num), YI_old 1 1 (by norm_num), YI_old 2 1 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num), YI_new 2 m 0 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_0_1_1 (m : ℕ) : D3g 0 1 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 0 1 (14 + 4*m + 1) = (550854000 : ℤ) * ((m : ℤ) + 1) + (54809973000) := by
    rw [D3g, YI_old 0 0 (by norm_num), YI_old 1 0 (by norm_num), YI_old 2 0 (by norm_num),
        YI_old 0 1 (by norm_num), YI_old 1 1 (by norm_num), YI_old 2 1 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_0_1_2 (m : ℕ) : D3g 0 1 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 0 1 (14 + 4*m + 2) = (-1652562000 : ℤ) * ((m : ℤ) + 1) + (-53432838000) := by
    rw [D3g, YI_old 0 0 (by norm_num), YI_old 1 0 (by norm_num), YI_old 2 0 (by norm_num),
        YI_old 0 1 (by norm_num), YI_old 1 1 (by norm_num), YI_old 2 1 (by norm_num),
        YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_0_1_3 (m : ℕ) : D3g 0 1 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 0 1 (14 + 4*m + 3) = (0 : ℤ) * ((m : ℤ) + 1) + (111823362000) := by
    rw [D3g, YI_old 0 0 (by norm_num), YI_old 1 0 (by norm_num), YI_old 2 0 (by norm_num),
        YI_old 0 1 (by norm_num), YI_old 1 1 (by norm_num), YI_old 2 1 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_2_3_0 (m : ℕ) : D3g 2 3 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 2 3 (14 + 4*m + 0) = (-302969700 : ℤ) * ((m : ℤ) + 1) + (-605939400) := by
    rw [D3g, YI_old 0 2 (by norm_num), YI_old 1 2 (by norm_num), YI_old 2 2 (by norm_num),
        YI_old 0 3 (by norm_num), YI_old 1 3 (by norm_num), YI_old 2 3 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num), YI_new 2 m 0 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_2_3_1 (m : ℕ) : D3g 2 3 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 2 3 (14 + 4*m + 1) = (0 : ℤ) * ((m : ℤ) + 1) + (1872903600) := by
    rw [D3g, YI_old 0 2 (by norm_num), YI_old 1 2 (by norm_num), YI_old 2 2 (by norm_num),
        YI_old 0 3 (by norm_num), YI_old 1 3 (by norm_num), YI_old 2 3 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_2_3_2 (m : ℕ) : D3g 2 3 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 2 3 (14 + 4*m + 2) = (605939400 : ℤ) * ((m : ℤ) + 1) + (-661024800) := by
    rw [D3g, YI_old 0 2 (by norm_num), YI_old 1 2 (by norm_num), YI_old 2 2 (by norm_num),
        YI_old 0 3 (by norm_num), YI_old 1 3 (by norm_num), YI_old 2 3 (by norm_num),
        YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_2_3_3 (m : ℕ) : D3g 2 3 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 2 3 (14 + 4*m + 3) = (605939400 : ℤ) * ((m : ℤ) + 1) + (4654716300) := by
    rw [D3g, YI_old 0 2 (by norm_num), YI_old 1 2 (by norm_num), YI_old 2 2 (by norm_num),
        YI_old 0 3 (by norm_num), YI_old 1 3 (by norm_num), YI_old 2 3 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_4_5_0 (m : ℕ) : D3g 4 5 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 4 5 (14 + 4*m + 0) = (-4751115750 : ℤ) * ((m : ℤ) + 1) + (-6128250750) := by
    rw [D3g, YI_old 0 4 (by norm_num), YI_old 1 4 (by norm_num), YI_old 2 4 (by norm_num),
        YI_old 0 5 (by norm_num), YI_old 1 5 (by norm_num), YI_old 2 5 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num), YI_new 2 m 0 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_4_5_1 (m : ℕ) : D3g 4 5 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 4 5 (14 + 4*m + 1) = (-963994500 : ℤ) * ((m : ℤ) + 1) + (-66653334000) := by
    rw [D3g, YI_old 0 4 (by norm_num), YI_old 1 4 (by norm_num), YI_old 2 4 (by norm_num),
        YI_old 0 5 (by norm_num), YI_old 1 5 (by norm_num), YI_old 2 5 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_4_5_2 (m : ℕ) : D3g 4 5 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 4 5 (14 + 4*m + 2) = (10466226000 : ℤ) * ((m : ℤ) + 1) + (79391832750) := by
    rw [D3g, YI_old 0 4 (by norm_num), YI_old 1 4 (by norm_num), YI_old 2 4 (by norm_num),
        YI_old 0 5 (by norm_num), YI_old 1 5 (by norm_num), YI_old 2 5 (by norm_num),
        YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_4_5_3 (m : ℕ) : D3g 4 5 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 4 5 (14 + 4*m + 3) = (7574242500 : ℤ) * ((m : ℤ) + 1) + (-125801282250) := by
    rw [D3g, YI_old 0 4 (by norm_num), YI_old 1 4 (by norm_num), YI_old 2 4 (by norm_num),
        YI_old 0 5 (by norm_num), YI_old 1 5 (by norm_num), YI_old 2 5 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_6_7_0 (m : ℕ) : D3g 6 7 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 6 7 (14 + 4*m + 0) = (208865475 : ℤ) * ((m : ℤ) + 1) + (208865475) := by
    rw [D3g, YI_old 0 6 (by norm_num), YI_old 1 6 (by norm_num), YI_old 2 6 (by norm_num),
        YI_old 0 7 (by norm_num), YI_old 1 7 (by norm_num), YI_old 2 7 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num), YI_new 2 m 0 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_6_7_1 (m : ℕ) : D3g 6 7 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 6 7 (14 + 4*m + 1) = (59675850 : ℤ) * ((m : ℤ) + 1) + (4461917400) := by
    rw [D3g, YI_old 0 6 (by norm_num), YI_old 1 6 (by norm_num), YI_old 2 6 (by norm_num),
        YI_old 0 7 (by norm_num), YI_old 1 7 (by norm_num), YI_old 2 7 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_6_7_2 (m : ℕ) : D3g 6 7 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 6 7 (14 + 4*m + 2) = (-477406800 : ℤ) * ((m : ℤ) + 1) + (-4909486275) := by
    rw [D3g, YI_old 0 6 (by norm_num), YI_old 1 6 (by norm_num), YI_old 2 6 (by norm_num),
        YI_old 0 7 (by norm_num), YI_old 1 7 (by norm_num), YI_old 2 7 (by norm_num),
        YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_6_7_3 (m : ℕ) : D3g 6 7 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 6 7 (14 + 4*m + 3) = (-298379250 : ℤ) * ((m : ℤ) + 1) + (8714969325) := by
    rw [D3g, YI_old 0 6 (by norm_num), YI_old 1 6 (by norm_num), YI_old 2 6 (by norm_num),
        YI_old 0 7 (by norm_num), YI_old 1 7 (by norm_num), YI_old 2 7 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_10_11_0 (m : ℕ) : D3g 10 11 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 10 11 (14 + 4*m + 0) = (-1927989000 : ℤ) * ((m : ℤ) + 1) + (0) := by
    rw [D3g, YI_old 0 10 (by norm_num), YI_old 1 10 (by norm_num), YI_old 2 10 (by norm_num),
        YI_old 0 11 (by norm_num), YI_old 1 11 (by norm_num), YI_old 2 11 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num), YI_new 2 m 0 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_10_11_1 (m : ℕ) : D3g 10 11 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 10 11 (14 + 4*m + 1) = (-1101708000 : ℤ) * ((m : ℤ) + 1) + (0) := by
    rw [D3g, YI_old 0 10 (by norm_num), YI_old 1 10 (by norm_num), YI_old 2 10 (by norm_num),
        YI_old 0 11 (by norm_num), YI_old 1 11 (by norm_num), YI_old 2 11 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_10_11_2 (m : ℕ) : D3g 10 11 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 10 11 (14 + 4*m + 2) = (4957686000 : ℤ) * ((m : ℤ) + 1) + (550854000) := by
    rw [D3g, YI_old 0 10 (by norm_num), YI_old 1 10 (by norm_num), YI_old 2 10 (by norm_num),
        YI_old 0 11 (by norm_num), YI_old 1 11 (by norm_num), YI_old 2 11 (by norm_num),
        YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_10_11_3 (m : ℕ) : D3g 10 11 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 10 11 (14 + 4*m + 3) = (1652562000 : ℤ) * ((m : ℤ) + 1) + (-1927989000) := by
    rw [D3g, YI_old 0 10 (by norm_num), YI_old 1 10 (by norm_num), YI_old 2 10 (by norm_num),
        YI_old 0 11 (by norm_num), YI_old 1 11 (by norm_num), YI_old 2 11 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_12_13_0 (m : ℕ) : D3g 12 13 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 12 13 (14 + 4*m + 0) = (-286719507000 : ℤ) * ((m : ℤ) + 1) + (-826281000) := by
    rw [D3g, YI_old 0 12 (by norm_num), YI_old 1 12 (by norm_num), YI_old 2 12 (by norm_num),
        YI_old 0 13 (by norm_num), YI_old 1 13 (by norm_num), YI_old 2 13 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num), YI_new 2 m 0 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_12_13_1 (m : ℕ) : D3g 12 13 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 12 13 (14 + 4*m + 1) = (-163603638000 : ℤ) * ((m : ℤ) + 1) + (83454381000) := by
    rw [D3g, YI_old 0 12 (by norm_num), YI_old 1 12 (by norm_num), YI_old 2 12 (by norm_num),
        YI_old 0 13 (by norm_num), YI_old 1 13 (by norm_num), YI_old 2 13 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 1 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_12_13_2 (m : ℕ) : D3g 12 13 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 12 13 (14 + 4*m + 2) = (737042652000 : ℤ) * ((m : ℤ) + 1) + (0) := by
    rw [D3g, YI_old 0 12 (by norm_num), YI_old 1 12 (by norm_num), YI_old 2 12 (by norm_num),
        YI_old 0 13 (by norm_num), YI_old 1 13 (by norm_num), YI_old 2 13 (by norm_num),
        YI_new 0 m 2 (by norm_num), YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dB_12_13_3 (m : ℕ) : D3g 12 13 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : D3g 12 13 (14 + 4*m + 3) = (246231738000 : ℤ) * ((m : ℤ) + 1) + (-118158183000) := by
    rw [D3g, YI_old 0 12 (by norm_num), YI_old 1 12 (by norm_num), YI_old 2 12 (by norm_num),
        YI_old 0 13 (by norm_num), YI_old 1 13 (by norm_num), YI_old 2 13 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num), YI_new 2 m 3 (by norm_num)]
    norm_num [dt, Y3]
    ring
  rw [hform]
  omega

lemma dS_8_0 (m : ℕ) : M2 0 1 8 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 0 1 8 (14 + 4*m + 0) = (11415525 : ℤ) * ((m : ℤ) + 1) + (22353825) := by
    rw [M2, YI_old 0 8 (by norm_num), YI_old 1 8 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_8_1 (m : ℕ) : M2 0 2 8 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 0 2 8 (14 + 4*m + 1) = (1408950 : ℤ) * ((m : ℤ) + 1) + (274275600) := by
    rw [M2, YI_old 0 8 (by norm_num), YI_old 2 8 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_8_2 (m : ℕ) : M2 1 2 8 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 1 2 8 (14 + 4*m + 2) = (41935200 : ℤ) * ((m : ℤ) + 1) + (531946800) := by
    rw [M2, YI_old 1 8 (by norm_num), YI_old 2 8 (by norm_num),
        YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_8_3 (m : ℕ) : M2 0 1 8 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 0 1 8 (14 + 4*m + 3) = (-22558350 : ℤ) * ((m : ℤ) + 1) + (-205517325) := by
    rw [M2, YI_old 0 8 (by norm_num), YI_old 1 8 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_9_0 (m : ℕ) : M2 0 1 9 (14 + 4*m + 0) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 0 1 9 (14 + 4*m + 0) = (70379325 : ℤ) * ((m : ℤ) + 1) + (137736225) := by
    rw [M2, YI_old 0 9 (by norm_num), YI_old 1 9 (by norm_num),
        YI_new 0 m 0 (by norm_num), YI_new 1 m 0 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_9_1 (m : ℕ) : M2 0 2 9 (14 + 4*m + 1) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 0 2 9 (14 + 4*m + 1) = (8680950 : ℤ) * ((m : ℤ) + 1) + (1689649200) := by
    rw [M2, YI_old 0 9 (by norm_num), YI_old 2 9 (by norm_num),
        YI_new 0 m 1 (by norm_num), YI_new 2 m 1 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_9_2 (m : ℕ) : M2 1 2 9 (14 + 4*m + 2) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 1 2 9 (14 + 4*m + 2) = (258156000 : ℤ) * ((m : ℤ) + 1) + (3274854300) := by
    rw [M2, YI_old 1 9 (by norm_num), YI_old 2 9 (by norm_num),
        YI_new 1 m 2 (by norm_num), YI_new 2 m 2 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dS_9_3 (m : ℕ) : M2 0 1 9 (14 + 4*m + 3) ≠ 0 := by
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by omega
  have hform : M2 0 1 9 (14 + 4*m + 3) = (-139031550 : ℤ) * ((m : ℤ) + 1) + (-1262078325) := by
    rw [M2, YI_old 0 9 (by norm_num), YI_old 1 9 (by norm_num),
        YI_new 0 m 3 (by norm_num), YI_new 1 m 3 (by norm_num)]
    norm_num [Y3]
    ring
  rw [hform]
  omega

lemma dABn_form (m m' tt : ℕ) (htt : tt < 4) :
    D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + tt)
      = 181800 * ((2*(YI 0 (14+4*m'+tt)) - (YI 1 (14+4*m'+tt)) + 5*(YI 2 (14+4*m'+tt)))
            * (((m : ℤ) + 1))^2
          + (293*(YI 0 (14+4*m'+tt)) - 160*(YI 1 (14+4*m'+tt)) + 536*(YI 2 (14+4*m'+tt)))
            * ((m : ℤ) + 1)
          + (445*(YI 0 (14+4*m'+tt)) - 302*(YI 1 (14+4*m'+tt)) + 898*(YI 2 (14+4*m'+tt)))) := by
  rw [D3g, dAB_form]

lemma dCDn_form (m m' tt : ℕ) (htt : tt < 4) :
    D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + tt)
      = -272700 * (4*(2*(YI 0 (14+4*m'+tt)) - (YI 1 (14+4*m'+tt)) + 5*(YI 2 (14+4*m'+tt)))
            * (((m : ℤ) + 1))^2
          + 4*(293*(YI 0 (14+4*m'+tt)) - 160*(YI 1 (14+4*m'+tt)) + 536*(YI 2 (14+4*m'+tt)))
            * ((m : ℤ) + 1)
          + (1624*(YI 0 (14+4*m'+tt)) - 1111*(YI 1 (14+4*m'+tt)) + 3299*(YI 2 (14+4*m'+tt)))) := by
  rw [D3g, dCD_form]

lemma dABn0 (m m' : ℕ) (h : m ≠ m') : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 0) ≠ 0 := by
  have hform : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 0)
      = 23135868000 * (((m' : ℤ) + 1) - ((m : ℤ) + 1)) := by
    rw [dABn_form m m' 0 (by norm_num), YI_new 0 m' 0 (by norm_num),
        YI_new 1 m' 0 (by norm_num), YI_new 2 m' 0 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  have h1 : ((m' : ℤ) + 1) - ((m : ℤ) + 1) ≠ 0 := by
    have : (m : ℤ) ≠ (m' : ℤ) := by exact_mod_cast h
    omega
  exact mul_ne_zero (by norm_num) h1

lemma dABn1 (m m' : ℕ) (h : m ≠ m') : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 1) ≠ 0 := by
  have hform : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 1)
      = -6610248000 * (((m : ℤ) + 1) + 2) * (((m : ℤ) + 1) - ((m' : ℤ) + 1)) := by
    rw [dABn_form m m' 1 (by norm_num), YI_new 0 m' 1 (by norm_num),
        YI_new 1 m' 1 (by norm_num), YI_new 2 m' 1 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  have h1 : ((m : ℤ) + 1) + 2 ≠ 0 := by
    have : (0:ℤ) ≤ (m : ℤ) := Int.ofNat_nonneg m
    omega
  have h2 : ((m : ℤ) + 1) - ((m' : ℤ) + 1) ≠ 0 := by
    have : (m : ℤ) ≠ (m' : ℤ) := by exact_mod_cast h
    omega
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2

lemma dABn2 (m m' : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 2) ≠ 0 := by
  have hform : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 2)
      = 3305124000 * (2*((m : ℤ) + 1)^2 - 2*((m : ℤ)+1)*((m' : ℤ)+1) + 17*((m : ℤ)+1)
          - 18*((m' : ℤ)+1) - 2) := by
    rw [dABn_form m m' 2 (by norm_num), YI_new 0 m' 2 (by norm_num),
        YI_new 1 m' 2 (by norm_num), YI_new 2 m' 2 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  have hX : (1:ℤ) ≤ (m : ℤ) + 1 := by
    have : (0:ℤ) ≤ (m : ℤ) := Int.ofNat_nonneg m
    omega
  have hY : (1:ℤ) ≤ (m' : ℤ) + 1 := by
    have : (0:ℤ) ≤ (m' : ℤ) := Int.ofNat_nonneg m'
    omega
  intro hc
  have hz : 2*((m : ℤ) + 1)^2 - 2*((m : ℤ)+1)*((m' : ℤ)+1) + 17*((m : ℤ)+1)
      - 18*((m' : ℤ)+1) - 2 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (by norm_num)
    · exact h
  have e1 : (2*((m : ℤ)+1) + 18) * (((m' : ℤ)+1) - ((m : ℤ)+1) + 1) = ((m : ℤ)+1) + 16 := by
    linear_combination -hz
  have hpos : (0:ℤ) ≤ 2*((m : ℤ)+1) + 18 := by linarith
  rcases le_or_gt (((m' : ℤ)+1) - ((m : ℤ)+1) + 1) 0 with hb | hb
  · have hle := mul_le_mul_of_nonneg_left hb hpos
    rw [mul_zero] at hle
    linarith [e1 ▸ hle]
  · have hb' : (1:ℤ) ≤ ((m' : ℤ)+1) - ((m : ℤ)+1) + 1 := hb
    have hle := mul_le_mul_of_nonneg_left hb' hpos
    rw [mul_one] at hle
    linarith [e1 ▸ hle]

lemma dABn3 (m m' : ℕ) : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 3) ≠ 0 := by
  have hform : D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + 3)
      = -3305124000 * (4*((m : ℤ) + 1)^2 - 4*((m : ℤ)+1)*((m' : ℤ)+1) - 6*((m : ℤ)+1)
          + 6*((m' : ℤ)+1) - 7) := by
    rw [dABn_form m m' 3 (by norm_num), YI_new 0 m' 3 (by norm_num),
        YI_new 1 m' 3 (by norm_num), YI_new 2 m' 3 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  intro hc
  have hz : 4*((m : ℤ) + 1)^2 - 4*((m : ℤ)+1)*((m' : ℤ)+1) - 6*((m : ℤ)+1)
      + 6*((m' : ℤ)+1) - 7 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (by norm_num)
    · exact h
  set t : ℤ := 2*((m : ℤ) + 1)^2 - 2*((m : ℤ)+1)*((m' : ℤ)+1) - 3*((m : ℤ)+1)
      + 3*((m' : ℤ)+1) with ht
  have h2 : 2 * t = 7 := by rw [ht]; linear_combination hz
  omega

lemma dCDn0 (m m' : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 0) ≠ 0 := by
  have hform : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 0)
      = 3305124000 * (42*((m : ℤ)+1) - 40*((m' : ℤ)+1) - 3) := by
    rw [dCDn_form m m' 0 (by norm_num), YI_new 0 m' 0 (by norm_num),
        YI_new 1 m' 0 (by norm_num), YI_new 2 m' 0 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  have h1 : 42*((m : ℤ)+1) - 40*((m' : ℤ)+1) - 3 ≠ 0 := by omega
  exact mul_ne_zero (by norm_num) h1

lemma dCDn1 (m m' : ℕ) : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 1) ≠ 0 := by
  have hform : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 1)
      = 3305124000 * (12*((m : ℤ)+1)^2 - 12*((m : ℤ)+1)*((m' : ℤ)+1) + 24*((m : ℤ)+1)
          - 22*((m' : ℤ)+1) + 17) := by
    rw [dCDn_form m m' 1 (by norm_num), YI_new 0 m' 1 (by norm_num),
        YI_new 1 m' 1 (by norm_num), YI_new 2 m' 1 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  intro hc
  have hz : 12*((m : ℤ)+1)^2 - 12*((m : ℤ)+1)*((m' : ℤ)+1) + 24*((m : ℤ)+1)
      - 22*((m' : ℤ)+1) + 17 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (by norm_num)
    · exact h
  set t : ℤ := 6*((m : ℤ)+1)^2 - 6*((m : ℤ)+1)*((m' : ℤ)+1) + 12*((m : ℤ)+1)
      - 11*((m' : ℤ)+1) with ht
  have h2 : 2 * t = -17 := by rw [ht]; linear_combination hz
  omega

lemma dCDn2 (m m' : ℕ) (h : m ≠ m') : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 2) ≠ 0 := by
  have hform : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 2)
      = -19830744000 * (((m : ℤ)+1) - ((m' : ℤ)+1)) * (2*((m : ℤ)+1) + 17) := by
    rw [dCDn_form m m' 2 (by norm_num), YI_new 0 m' 2 (by norm_num),
        YI_new 1 m' 2 (by norm_num), YI_new 2 m' 2 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  have h1 : ((m : ℤ)+1) - ((m' : ℤ)+1) ≠ 0 := by
    have : (m : ℤ) ≠ (m' : ℤ) := by exact_mod_cast h
    omega
  have h2 : 2*((m : ℤ)+1) + 17 ≠ 0 := by
    have : (0:ℤ) ≤ (m : ℤ) := Int.ofNat_nonneg m
    omega
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2

lemma dCDn3 (m m' : ℕ) (h : m ≠ m') : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 3) ≠ 0 := by
  have hform : D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + 3)
      = 39661488000 * (((m : ℤ)+1) - ((m' : ℤ)+1)) * (2*((m : ℤ)+1) - 3) := by
    rw [dCDn_form m m' 3 (by norm_num), YI_new 0 m' 3 (by norm_num),
        YI_new 1 m' 3 (by norm_num), YI_new 2 m' 3 (by norm_num)]
    norm_num [Y3]; ring
  rw [hform]
  have h1 : ((m : ℤ)+1) - ((m' : ℤ)+1) ≠ 0 := by
    have : (m : ℤ) ≠ (m' : ℤ) := by exact_mod_cast h
    omega
  have h2 : 2*((m : ℤ)+1) - 3 ≠ 0 := by
    have : (0:ℤ) ≤ (m : ℤ) := Int.ofNat_nonneg m
    omega
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2




open Finset

/-! ## Class representatives -/

/-- First representative of `u`-class `k`. -/
def cp (k : ℕ) : ℕ :=
  if k ≤ 3 then 2 * k
  else if k = 4 then 8
  else if k = 5 then 9
  else if k ≤ 7 then 2 * k - 2
  else 14 + 4 * ((k - 8) / 2) + 2 * ((k - 8) % 2)

/-- Second representative of `u`-class `k` (equal to `cp k` for the singleton classes 4, 5). -/
def cq (k : ℕ) : ℕ := if k = 4 then 8 else if k = 5 then 9 else cp k + 1

lemma cp_lt_cq (k : ℕ) (h4 : k ≠ 4) (h5 : k ≠ 5) : cp k < cq k := by
  simp [cq, h4, h5]

lemma cls_cp (k : ℕ) (hk : k ≠ 4) (hk5 : k ≠ 5) : cp k < cq k := cp_lt_cq k hk hk5

lemma cp_lt' (M k : ℕ) (hk : k < 8 + 2 * M) : cp k + 1 < 14 + 4 * M := by
  unfold cp
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · have h1 : (k - 8) / 2 < M := by omega
          have h2 : (k - 8) % 2 < 2 := by omega
          omega

lemma cp_lt (M k : ℕ) (hk : k < 8 + 2 * M) : cp k < 14 + 4 * M := by
  have := cp_lt' M k hk; omega

lemma cq_lt (M k : ℕ) (hk : k < 8 + 2 * M) : cq k < 14 + 4 * M := by
  unfold cq
  split
  · omega
  · split
    · omega
    · have := cp_lt' M k hk; omega

lemma clsI_lt (M i : ℕ) (hi : i < 14 + 4 * M) : clsI i < 8 + 2 * M := by
  unfold clsI
  split
  · rename_i h
    interval_cases i <;> simp <;> omega
  · rename_i h
    have h1 : (i - 14) / 4 < M := by omega
    have h2 : (i - 14) % 4 < 4 := by omega
    omega

lemma clsCovBase : ∀ i ∈ List.range 14, i = cp (clsI i) ∨ i = cq (clsI i) := by decide

lemma clsCov (M i : ℕ) (hi : i < 14 + 4 * M) : i = cp (clsI i) ∨ i = cq (clsI i) := by
  by_cases h : i < 14
  · exact clsCovBase i (List.mem_range.mpr h)
  · push_neg at h
    obtain ⟨mm, tt, htt, rfl⟩ : ∃ mm tt, tt < 4 ∧ i = 14 + 4 * mm + tt :=
      ⟨(i - 14) / 4, (i - 14) % 4, by omega, by omega⟩
    rw [clsI_new mm tt htt]
    have hk : ¬ (8 + 2 * mm + tt / 2 ≤ 3) := by omega
    have hk4 : 8 + 2 * mm + tt / 2 ≠ 4 := by omega
    have hk5 : 8 + 2 * mm + tt / 2 ≠ 5 := by omega
    have hk7 : ¬ (8 + 2 * mm + tt / 2 ≤ 7) := by omega
    have e1 : (8 + 2 * mm + tt / 2 - 8) / 2 = mm := by omega
    have e2 : (8 + 2 * mm + tt / 2 - 8) % 2 = tt / 2 := by omega
    simp only [cq, cp, hk, hk4, hk5, hk7, if_false, e1, e2]
    interval_cases tt <;> simp <;> omega

/-! ## Non-vanishing of the relevant 3x3 determinants -/

lemma b01 : ∀ j ∈ List.range 14, j ≠ 0 → j ≠ 1 → D3g 0 1 j ≠ 0 := by decide
lemma b23 : ∀ j ∈ List.range 14, j ≠ 2 → j ≠ 3 → D3g 2 3 j ≠ 0 := by decide
lemma b45 : ∀ j ∈ List.range 14, j ≠ 4 → j ≠ 5 → D3g 4 5 j ≠ 0 := by decide
lemma b67 : ∀ j ∈ List.range 14, j ≠ 6 → j ≠ 7 → D3g 6 7 j ≠ 0 := by decide
lemma b1011 : ∀ j ∈ List.range 14, j ≠ 10 → j ≠ 11 → D3g 10 11 j ≠ 0 := by decide
lemma b1213 : ∀ j ∈ List.range 14, j ≠ 12 → j ≠ 13 → D3g 12 13 j ≠ 0 := by decide

lemma pairDet (p q : ℕ)
    (hbase : ∀ j ∈ List.range 14, j ≠ p → j ≠ q → D3g p q j ≠ 0)
    (hnew : ∀ m tt, tt < 4 → 14 + 4*m + tt ≠ p → 14 + 4*m + tt ≠ q →
      D3g p q (14 + 4*m + tt) ≠ 0)
    (j : ℕ) (hjp : j ≠ p) (hjq : j ≠ q) : D3g p q j ≠ 0 := by
  by_cases h : j < 14
  · exact hbase j (List.mem_range.mpr h) hjp hjq
  · obtain ⟨m, tt, htt, rfl⟩ : ∃ m tt, tt < 4 ∧ j = 14 + 4 * m + tt :=
      ⟨(j - 14) / 4, (j - 14) % 4, by omega, by omega⟩
    exact hnew m tt htt hjp hjq

lemma abBase (m : ℕ) : ∀ j ∈ List.range 14, j ≠ 14 + 4*m → j ≠ 14 + 4*m + 1 →
    D3g (14 + 4*m) (14 + 4*m + 1) j ≠ 0 := by
  intro j hj _ _
  have hj' : j < 14 := List.mem_range.mp hj
  interval_cases j
  exacts [dAB_ne_b0 m, dAB_ne_b1 m, dAB_ne_b2 m, dAB_ne_b3 m, dAB_ne_b4 m, dAB_ne_b5 m,
    dAB_ne_b6 m, dAB_ne_b7 m, dAB_ne_b8 m, dAB_ne_b9 m, dAB_ne_b10 m, dAB_ne_b11 m,
    dAB_ne_b12 m, dAB_ne_b13 m]

lemma cdBase (m : ℕ) : ∀ j ∈ List.range 14, j ≠ 14 + 4*m + 2 → j ≠ 14 + 4*m + 3 →
    D3g (14 + 4*m + 2) (14 + 4*m + 3) j ≠ 0 := by
  intro j hj _ _
  have hj' : j < 14 := List.mem_range.mp hj
  interval_cases j
  exacts [dCD_ne_b0 m, dCD_ne_b1 m, dCD_ne_b2 m, dCD_ne_b3 m, dCD_ne_b4 m, dCD_ne_b5 m,
    dCD_ne_b6 m, dCD_ne_b7 m, dCD_ne_b8 m, dCD_ne_b9 m, dCD_ne_b10 m, dCD_ne_b11 m,
    dCD_ne_b12 m, dCD_ne_b13 m]

lemma abNew (m : ℕ) : ∀ m' tt, tt < 4 → 14 + 4*m' + tt ≠ 14 + 4*m →
    14 + 4*m' + tt ≠ 14 + 4*m + 1 → D3g (14 + 4*m) (14 + 4*m + 1) (14 + 4*m' + tt) ≠ 0 := by
  intro m' tt htt h0 h1
  interval_cases tt
  · exact dABn0 m m' (by omega)
  · exact dABn1 m m' (by omega)
  · exact dABn2 m m'
  · exact dABn3 m m'

lemma cdNew (m : ℕ) : ∀ m' tt, tt < 4 → 14 + 4*m' + tt ≠ 14 + 4*m + 2 →
    14 + 4*m' + tt ≠ 14 + 4*m + 3 →
    D3g (14 + 4*m + 2) (14 + 4*m + 3) (14 + 4*m' + tt) ≠ 0 := by
  intro m' tt htt h0 h1
  interval_cases tt
  · exact dCDn0 m m'
  · exact dCDn1 m m'
  · exact dCDn2 m m' (by omega)
  · exact dCDn3 m m' (by omega)

lemma cp_val (k : ℕ) (h3 : ¬ (k ≤ 3)) (h4 : k ≠ 4) (h5 : k ≠ 5) (h7 : ¬ (k ≤ 7)) :
    cp k = 14 + 4 * ((k - 8) / 2) + 2 * ((k - 8) % 2) := by
  unfold cp; rw [if_neg h3, if_neg h4, if_neg h5, if_neg h7]

lemma cq_val (k : ℕ) (h4 : k ≠ 4) (h5 : k ≠ 5) : cq k = cp k + 1 := by
  unfold cq; rw [if_neg h4, if_neg h5]

lemma mainDet (M k j : ℕ) (hk : k < 8 + 2 * M) (h4 : k ≠ 4) (h5 : k ≠ 5)
    (hjp : j ≠ cp k) (hjq : j ≠ cq k) : D3g (cp k) (cq k) j ≠ 0 := by
  by_cases hk8 : k ≤ 7
  · interval_cases k
    · have e1 : cp 0 = 0 := by norm_num [cp]
      have e2 : cq 0 = 1 := by norm_num [cq, cp]
      rw [e1] at hjp
      rw [e2] at hjq
      rw [e1, e2]
      refine pairDet 0 1 b01 (fun m tt htt _ _ => ?_) j hjp hjq
      interval_cases tt
      exacts [dB_0_1_0 m, dB_0_1_1 m, dB_0_1_2 m, dB_0_1_3 m]
    · have e1 : cp 1 = 2 := by norm_num [cp]
      have e2 : cq 1 = 3 := by norm_num [cq, cp]
      rw [e1] at hjp
      rw [e2] at hjq
      rw [e1, e2]
      refine pairDet 2 3 b23 (fun m tt htt _ _ => ?_) j hjp hjq
      interval_cases tt
      exacts [dB_2_3_0 m, dB_2_3_1 m, dB_2_3_2 m, dB_2_3_3 m]
    · have e1 : cp 2 = 4 := by norm_num [cp]
      have e2 : cq 2 = 5 := by norm_num [cq, cp]
      rw [e1] at hjp
      rw [e2] at hjq
      rw [e1, e2]
      refine pairDet 4 5 b45 (fun m tt htt _ _ => ?_) j hjp hjq
      interval_cases tt
      exacts [dB_4_5_0 m, dB_4_5_1 m, dB_4_5_2 m, dB_4_5_3 m]
    · have e1 : cp 3 = 6 := by norm_num [cp]
      have e2 : cq 3 = 7 := by norm_num [cq, cp]
      rw [e1] at hjp
      rw [e2] at hjq
      rw [e1, e2]
      refine pairDet 6 7 b67 (fun m tt htt _ _ => ?_) j hjp hjq
      interval_cases tt
      exacts [dB_6_7_0 m, dB_6_7_1 m, dB_6_7_2 m, dB_6_7_3 m]
    · exact absurd rfl (by assumption)
    · exact absurd rfl (by assumption)
    · have e1 : cp 6 = 10 := by norm_num [cp]
      have e2 : cq 6 = 11 := by norm_num [cq, cp]
      rw [e1] at hjp
      rw [e2] at hjq
      rw [e1, e2]
      refine pairDet 10 11 b1011 (fun m tt htt _ _ => ?_) j hjp hjq
      interval_cases tt
      exacts [dB_10_11_0 m, dB_10_11_1 m, dB_10_11_2 m, dB_10_11_3 m]
    · have e1 : cp 7 = 12 := by norm_num [cp]
      have e2 : cq 7 = 13 := by norm_num [cq, cp]
      rw [e1] at hjp
      rw [e2] at hjq
      rw [e1, e2]
      refine pairDet 12 13 b1213 (fun m tt htt _ _ => ?_) j hjp hjq
      interval_cases tt
      exacts [dB_12_13_0 m, dB_12_13_1 m, dB_12_13_2 m, dB_12_13_3 m]
  · have h3 : ¬ (k ≤ 3) := by omega
    have hcp := cp_val k h3 h4 h5 hk8
    have hcq : cq k = cp k + 1 := cq_val k h4 h5
    obtain ⟨m, e, he, hke⟩ : ∃ m e, e < 2 ∧ k = 8 + 2*m + e :=
      ⟨(k - 8) / 2, (k - 8) % 2, by omega, by omega⟩
    have hA : (k - 8) / 2 = m := by omega
    have hB : (k - 8) % 2 = e := by omega
    rw [hA, hB] at hcp
    interval_cases e
    · have hcp0 : cp k = 14 + 4*m := by omega
      have hcq0 : cq k = 14 + 4*m + 1 := by omega
      rw [hcp0] at hjp
      rw [hcq0] at hjq
      rw [hcp0, hcq0]
      exact pairDet (14 + 4*m) (14 + 4*m + 1) (abBase m) (abNew m) j hjp hjq
    · have hcp1 : cp k = 14 + 4*m + 2 := by omega
      have hcq1 : cq k = 14 + 4*m + 3 := by omega
      rw [hcp1] at hjp
      rw [hcq1] at hjq
      rw [hcp1, hcq1]
      exact pairDet (14 + 4*m + 2) (14 + 4*m + 3) (cdBase m) (cdNew m) j hjp hjq


/-! ## The 2 x 2 minors used for the two singleton classes -/

lemma m2b8 : ∀ j ∈ List.range 14, j ≠ 8 →
    (M2 0 1 8 j ≠ 0 ∨ M2 0 2 8 j ≠ 0 ∨ M2 1 2 8 j ≠ 0) := by decide

lemma m2b9 : ∀ j ∈ List.range 14, j ≠ 9 →
    (M2 0 1 9 j ≠ 0 ∨ M2 0 2 9 j ≠ 0 ∨ M2 1 2 9 j ≠ 0) := by decide

lemma minorDet (c j : ℕ) (hc : c = 8 ∨ c = 9) (hj : j ≠ c) :
    M2 0 1 c j ≠ 0 ∨ M2 0 2 c j ≠ 0 ∨ M2 1 2 c j ≠ 0 := by
  have hsplit : ∀ (d : ℕ), (∀ j ∈ List.range 14, j ≠ d →
      (M2 0 1 d j ≠ 0 ∨ M2 0 2 d j ≠ 0 ∨ M2 1 2 d j ≠ 0)) →
      (∀ m, M2 0 1 d (14 + 4*m + 0) ≠ 0) → (∀ m, M2 0 2 d (14 + 4*m + 1) ≠ 0) →
      (∀ m, M2 1 2 d (14 + 4*m + 2) ≠ 0) → (∀ m, M2 0 1 d (14 + 4*m + 3) ≠ 0) →
      j ≠ d → (M2 0 1 d j ≠ 0 ∨ M2 0 2 d j ≠ 0 ∨ M2 1 2 d j ≠ 0) := by
    intro d hb f0 f1 f2 f3 hjd
    by_cases h : j < 14
    · exact hb j (List.mem_range.mpr h) hjd
    · obtain ⟨m, tt, htt, rfl⟩ : ∃ m tt, tt < 4 ∧ j = 14 + 4 * m + tt :=
        ⟨(j - 14) / 4, (j - 14) % 4, by omega, by omega⟩
      interval_cases tt
      · exact Or.inl (f0 m)
      · exact Or.inr (Or.inl (f1 m))
      · exact Or.inr (Or.inr (f2 m))
      · exact Or.inl (f3 m)
  rcases hc with rfl | rfl
  · exact hsplit 8 m2b8 dS_8_0 dS_8_1 dS_8_2 dS_8_3 hj
  · exact hsplit 9 m2b9 dS_9_0 dS_9_1 dS_9_2 dS_9_3 hj

/-! ## The `w`-directions are pairwise non-parallel -/

lemma wpBaseDec : ∀ i ∈ List.range 14, ∀ j ∈ List.range 14, i ≠ j →
    wsI i = wsI j → wpI 1 i ≠ wpI 1 j := by decide

lemma wpBase0 : ∀ i ∈ List.range 14, wsI i = 0 → wpI 1 i ≤ 6 := by decide

lemma wpBase1 : ∀ i ∈ List.range 14, wsI i = 1 →
    (wpI 1 i ≤ 4 ∨ wpI 1 i = 9 ∨ wpI 1 i = 10) := by decide

lemma wsBaseCases : ∀ i ∈ List.range 14, wsI i = 0 ∨ wsI i = 1 := by decide

/-- One-sided version of the injectivity of `i ↦ (wpI M i, wsI i)`. -/
lemma wpInj_mixed (M i mm tt : ℕ) (hM : 1 ≤ M) (hi : i < 14) (hmm : mm < M) (htt : tt < 4)
    (hs : wsI i = wsI (14 + 4 * mm + tt)) : wpI M i ≠ wpI M (14 + 4 * mm + tt) := by
  rw [wpI_old M i hM hi, wpI_new M mm tt htt]
  rw [wsI_new mm tt htt] at hs
  interval_cases tt
  · have h1 : wsI i = 1 := by simpa using hs
    have h2 := wpBase1 i (List.mem_range.mpr hi) h1
    split_ifs <;> first | contradiction | omega
  · have h1 : wsI i = 0 := by simpa using hs
    have h2 := wpBase0 i (List.mem_range.mpr hi) h1
    split_ifs <;> first | contradiction | omega
  · have h1 : wsI i = 1 := by simpa using hs
    have h2 := wpBase1 i (List.mem_range.mpr hi) h1
    split_ifs <;> first | contradiction | omega
  · have h1 : wsI i = 0 := by simpa using hs
    have h2 := wpBase0 i (List.mem_range.mpr hi) h1
    split_ifs <;> first | contradiction | omega

lemma wpInj_new (M mm tt mm' tt' : ℕ) (hmm : mm < M) (hmm' : mm' < M)
    (htt : tt < 4) (htt' : tt' < 4) (hne : ¬ (mm = mm' ∧ tt = tt'))
    (hs : wsI (14 + 4 * mm + tt) = wsI (14 + 4 * mm' + tt')) :
    wpI M (14 + 4 * mm + tt) ≠ wpI M (14 + 4 * mm' + tt') := by
  have hne' : mm ≠ mm' ∨ tt ≠ tt' := by tauto
  have hpar : tt % 2 = tt' % 2 := by
    rw [wsI_new mm tt htt, wsI_new mm' tt' htt'] at hs
    by_cases a : tt = 0 ∨ tt = 2 <;> by_cases b : tt' = 0 ∨ tt' = 2
    · rcases a with rfl | rfl <;> rcases b with rfl | rfl <;> rfl
    · rw [if_pos a, if_neg b] at hs; exact absurd hs (by norm_num)
    · rw [if_neg a, if_pos b] at hs; exact absurd hs (by norm_num)
    · push_neg at a b; omega
  rw [wpI_new M mm tt htt, wpI_new M mm' tt' htt']
  interval_cases tt <;> interval_cases tt' <;> split_ifs <;> first | contradiction | omega


lemma wpInj (M i j : ℕ) (hM : 1 ≤ M) (hi : i < 14 + 4 * M) (hj : j < 14 + 4 * M)
    (hij : i ≠ j) (hs : wsI i = wsI j) : wpI M i ≠ wpI M j := by
  rcases decomp M i hi with hio | ⟨mm, tt, hmm, htt, rfl⟩
  · rcases decomp M j hj with hjo | ⟨mm', tt', hmm', htt', rfl⟩
    · rw [wpI_old M i hM hio, wpI_old M j hM hjo]
      exact wpBaseDec i (List.mem_range.mpr hio) j (List.mem_range.mpr hjo) hij hs
    · exact wpInj_mixed M i mm' tt' hM hio hmm' htt' hs
  · rcases decomp M j hj with hjo | ⟨mm', tt', hmm', htt', rfl⟩
    · exact fun h => wpInj_mixed M j mm tt hM hjo hmm htt hs.symm h.symm
    · refine wpInj_new M mm tt mm' tt' hmm hmm' htt htt' ?_ hs
      rintro ⟨rfl, rfl⟩; exact hij rfl

/-! ## Non-parallelism of the first two factors -/

lemma WI0v (M i : ℕ) (h : wsI i = 0) : WI M i 0 = 1 ∧ WI M i 1 = (wpI M i : ℤ) + 1 := by
  constructor <;> simp [WI, h]

lemma WI1v (M i : ℕ) (h : wsI i = 1) :
    WI M i 0 = -((wpI M i : ℤ) + 1) ∧ WI M i 1 = 1 := by
  constructor <;> simp [WI, h]

lemma detW (M i j : ℕ) (hM : 1 ≤ M) (hi : i < 14 + 4 * M) (hj : j < 14 + 4 * M)
    (hij : i ≠ j) : WI M i 0 * WI M j 1 - WI M j 0 * WI M i 1 ≠ 0 := by
  have hp : (0:ℤ) ≤ (wpI M i : ℤ) := Int.natCast_nonneg _
  have hq : (0:ℤ) ≤ (wpI M j : ℤ) := Int.natCast_nonneg _
  rcases wsI_cases i with h1 | h1 <;> rcases wsI_cases j with h2 | h2
  · obtain ⟨a0, a1⟩ := WI0v M i h1
    obtain ⟨b0, b1⟩ := WI0v M j h2
    have hne : wpI M i ≠ wpI M j := wpInj M i j hM hi hj hij (by rw [h1, h2])
    have hz : ((wpI M i : ℤ)) ≠ ((wpI M j : ℤ)) := by exact_mod_cast hne
    rw [a0, a1, b0, b1]; intro hc; exact hz (by linarith [hc])
  · obtain ⟨a0, a1⟩ := WI0v M i h1
    obtain ⟨b0, b1⟩ := WI1v M j h2
    rw [a0, a1, b0, b1]; nlinarith [hp, hq]
  · obtain ⟨a0, a1⟩ := WI1v M i h1
    obtain ⟨b0, b1⟩ := WI0v M j h2
    rw [a0, a1, b0, b1]; nlinarith [hp, hq]
  · obtain ⟨a0, a1⟩ := WI1v M i h1
    obtain ⟨b0, b1⟩ := WI1v M j h2
    have hne : wpI M i ≠ wpI M j := wpInj M i j hM hi hj hij (by rw [h1, h2])
    have hz : ((wpI M i : ℤ)) ≠ ((wpI M j : ℤ)) := by exact_mod_cast hne
    rw [a0, a1, b0, b1]; intro hc; exact hz (by linarith [hc])

lemma wpBaseDec0 : ∀ i ∈ List.range 14, ∀ j ∈ List.range 14, i ≠ j →
    wsI i = wsI j → wpI 0 i ≠ wpI 0 j := by decide

lemma wpInjAll (M i j : ℕ) (hi : i < 14 + 4 * M) (hj : j < 14 + 4 * M) (hij : i ≠ j)
    (hs : wsI i = wsI j) : wpI M i ≠ wpI M j := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact wpBaseDec0 i (List.mem_range.mpr (by omega)) j (List.mem_range.mpr (by omega)) hij hs
  · exact wpInj M i j hM hi hj hij hs

lemma detWAll (M i j : ℕ) (hi : i < 14 + 4 * M) (hj : j < 14 + 4 * M)
    (hij : i ≠ j) : WI M i 0 * WI M j 1 - WI M j 0 * WI M i 1 ≠ 0 := by
  have hp : (0:ℤ) ≤ (wpI M i : ℤ) := Int.natCast_nonneg _
  have hq : (0:ℤ) ≤ (wpI M j : ℤ) := Int.natCast_nonneg _
  rcases wsI_cases i with h1 | h1 <;> rcases wsI_cases j with h2 | h2
  · obtain ⟨a0, a1⟩ := WI0v M i h1
    obtain ⟨b0, b1⟩ := WI0v M j h2
    have hne : wpI M i ≠ wpI M j := wpInjAll M i j hi hj hij (by rw [h1, h2])
    have hz : ((wpI M i : ℤ)) ≠ ((wpI M j : ℤ)) := by exact_mod_cast hne
    rw [a0, a1, b0, b1]; intro hc; exact hz (by linarith [hc])
  · obtain ⟨a0, a1⟩ := WI0v M i h1
    obtain ⟨b0, b1⟩ := WI1v M j h2
    rw [a0, a1, b0, b1]; nlinarith [hp, hq]
  · obtain ⟨a0, a1⟩ := WI1v M i h1
    obtain ⟨b0, b1⟩ := WI0v M j h2
    rw [a0, a1, b0, b1]; nlinarith [hp, hq]
  · obtain ⟨a0, a1⟩ := WI1v M i h1
    obtain ⟨b0, b1⟩ := WI1v M j h2
    have hne : wpI M i ≠ wpI M j := wpInjAll M i j hi hj hij (by rw [h1, h2])
    have hz : ((wpI M i : ℤ)) ≠ ((wpI M j : ℤ)) := by exact_mod_cast hne
    rw [a0, a1, b0, b1]; intro hc; exact hz (by linarith [hc])

lemma UI0v (i : ℕ) (h : clsI i % 2 = 0) :
    UI i 0 = 1 ∧ UI i 1 = ((clsI i / 2 : ℕ) : ℤ) + 1 := by
  constructor <;> simp [UI, h]

lemma UI1v (i : ℕ) (h : clsI i % 2 = 1) :
    UI i 0 = -(((clsI i / 2 : ℕ) : ℤ) + 1) ∧ UI i 1 = 1 := by
  have h' : ¬ (clsI i % 2 = 0) := by omega
  constructor <;> simp [UI, h']

lemma detU (i j : ℕ) (hij : clsI i ≠ clsI j) :
    UI i 0 * UI j 1 - UI j 0 * UI i 1 ≠ 0 := by
  have hp : (0:ℤ) ≤ ((clsI i / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hq : (0:ℤ) ≤ ((clsI j / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hi2 : clsI i % 2 = 0 ∨ clsI i % 2 = 1 := by omega
  have hj2 : clsI j % 2 = 0 ∨ clsI j % 2 = 1 := by omega
  rcases hi2 with h1 | h1 <;> rcases hj2 with h2 | h2
  · obtain ⟨a0, a1⟩ := UI0v i h1
    obtain ⟨b0, b1⟩ := UI0v j h2
    have hne : clsI i / 2 ≠ clsI j / 2 := by omega
    have hz : ((clsI i / 2 : ℕ) : ℤ) ≠ ((clsI j / 2 : ℕ) : ℤ) := by exact_mod_cast hne
    rw [a0, a1, b0, b1]; intro hc; exact hz (by linarith [hc])
  · obtain ⟨a0, a1⟩ := UI0v i h1
    obtain ⟨b0, b1⟩ := UI1v j h2
    rw [a0, a1, b0, b1]; nlinarith [hp, hq]
  · obtain ⟨a0, a1⟩ := UI1v i h1
    obtain ⟨b0, b1⟩ := UI0v j h2
    rw [a0, a1, b0, b1]; nlinarith [hp, hq]
  · obtain ⟨a0, a1⟩ := UI1v i h1
    obtain ⟨b0, b1⟩ := UI1v j h2
    have hne : clsI i / 2 ≠ clsI j / 2 := by omega
    have hz : ((clsI i / 2 : ℕ) : ℤ) ≠ ((clsI j / 2 : ℕ) : ℤ) := by exact_mod_cast hne
    rw [a0, a1, b0, b1]; intro hc; exact hz (by linarith [hc])


/-! ## Elimination helpers -/

lemma tri2g {a1 a2 b1 b2 x y : ℂ} (h1 : a1*x + b1*y = 0) (h2 : a2*x + b2*y = 0)
    (hd : a1*b2 - a2*b1 ≠ 0) : x = 0 ∧ y = 0 := by
  constructor
  · have h : (a1*b2 - a2*b1) * x = 0 := by linear_combination b2*h1 - b1*h2
    exact (mul_eq_zero.mp h).resolve_left hd
  · have h : (a1*b2 - a2*b1) * y = 0 := by linear_combination a1*h2 - a2*h1
    exact (mul_eq_zero.mp h).resolve_left hd

lemma tri3g {a1 a2 a3 b1 b2 b3 e1 e2 e3 x y t : ℂ}
    (h1 : a1*x + b1*y + e1*t = 0) (h2 : a2*x + b2*y + e2*t = 0) (h3 : a3*x + b3*y + e3*t = 0)
    (hd : a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2) ≠ 0) :
    x = 0 ∧ y = 0 ∧ t = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2)) * x = 0 := by
      linear_combination (b2*e3-b3*e2)*h1 - (b1*e3-b3*e1)*h2 + (b1*e2-b2*e1)*h3
    exact (mul_eq_zero.mp h).resolve_left hd
  · have h : (a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2)) * y = 0 := by
      linear_combination (-(a2*e3-a3*e2))*h1 + (a1*e3-a3*e1)*h2 - (a1*e2-a2*e1)*h3
    exact (mul_eq_zero.mp h).resolve_left hd
  · have h : (a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2)) * t = 0 := by
      linear_combination (a2*b3-a3*b2)*h1 - (a1*b3-a3*b1)*h2 + (a1*b2-a2*b1)*h3
    exact (mul_eq_zero.mp h).resolve_left hd

lemma pick2 {a1 a2 a3 b1 b2 b3 x y : ℂ}
    (h1 : a1*x + b1*y = 0) (h2 : a2*x + b2*y = 0) (h3 : a3*x + b3*y = 0)
    (hd : a1*b2 - a2*b1 ≠ 0 ∨ a1*b3 - a3*b1 ≠ 0 ∨ a2*b3 - a3*b2 ≠ 0) : x = 0 ∧ y = 0 := by
  rcases hd with h | h | h
  · exact tri2g h1 h2 h
  · exact tri2g h1 h3 h
  · exact tri2g h2 h3 h

lemma expand3 (n p q j : ℕ) (hp : p < n) (hq : q < n) (hj : j < n)
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j) (f R : ℕ → ℂ)
    (hz : ∀ i, i < n → i ≠ p → i ≠ q → i ≠ j → R i = 0) :
    (∑ i ∈ Finset.range n, f i * R i) = f p * R p + f q * R q + f j * R j := by
  have hsub : ({p, q, j} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_range.mpr hp
    · exact Finset.mem_range.mpr hq
    · exact Finset.mem_range.mpr hj
  have hf : ∀ x ∈ Finset.range n, x ∉ ({p, q, j} : Finset ℕ) → f x * R x = 0 := by
    intro x hx hx2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx2
    rw [hz x (Finset.mem_range.mp hx) hx2.1 hx2.2.1 hx2.2.2, mul_zero]
  rw [← Finset.sum_subset hsub hf,
    Finset.sum_insert (by simp [hpq, hpj]), Finset.sum_insert (by simp [hqj]),
    Finset.sum_singleton]
  ring

lemma expand2 (n p j : ℕ) (hp : p < n) (hj : j < n) (hpj : p ≠ j) (f R : ℕ → ℂ)
    (hz : ∀ i, i < n → i ≠ p → i ≠ j → R i = 0) :
    (∑ i ∈ Finset.range n, f i * R i) = f p * R p + f j * R j := by
  have hsub : ({p, j} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr hp
    · exact Finset.mem_range.mpr hj
  have hf : ∀ x ∈ Finset.range n, x ∉ ({p, j} : Finset ℕ) → f x * R x = 0 := by
    intro x hx hx2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx2
    rw [hz x (Finset.mem_range.mp hx) hx2.1 hx2.2, mul_zero]
  rw [← Finset.sum_subset hsub hf, Finset.sum_insert (by simp [hpj]), Finset.sum_singleton]

lemma cp_pos (k : ℕ) (h : k ≠ 0) : 0 < cp k := by
  unfold cp; split_ifs <;> omega

lemma cq_pos (k : ℕ) : 0 < cq k := by
  unfold cq cp; split_ifs <;> omega

lemma cp0 : cp 0 = 0 := by decide
lemma cq0 : cq 0 = 1 := by decide
lemma cp4 : cp 4 = 8 := by decide
lemma cq4 : cq 4 = 8 := by decide
lemma cp5 : cp 5 = 9 := by decide
lemma cq5 : cq 5 = 9 := by decide


lemma expand3h (n p q j : ℕ) (hp : p < n) (hq : q < n) (hj : j < n)
    (hpq : p ≠ q) (hpj : p ≠ j) (hqj : q ≠ j) (f R : ℕ → ℂ)
    (hz : ∀ i, i < n → i ≠ p → i ≠ q → i ≠ j → R i = 0)
    (h : (∑ i ∈ Finset.range n, f i * R i) = 0) :
    f p * R p + f q * R q + f j * R j = 0 := by
  rw [← expand3 n p q j hp hq hj hpq hpj hqj f R hz]; exact h

lemma expand2h (n p j : ℕ) (hp : p < n) (hj : j < n) (hpj : p ≠ j) (f R : ℕ → ℂ)
    (hz : ∀ i, i < n → i ≠ p → i ≠ j → R i = 0)
    (h : (∑ i ∈ Finset.range n, f i * R i) = 0) :
    f p * R p + f j * R j = 0 := by
  rw [← expand2 n p j hp hj hpj f R hz]; exact h

lemma m2C (r1 r2 c j : ℕ) (h : M2 r1 r2 c j ≠ 0) :
    ((YI r1 c : ℤ) : ℂ) * ((YI r2 j : ℤ) : ℂ)
      - ((YI r2 c : ℤ) : ℂ) * ((YI r1 j : ℤ) : ℂ) ≠ 0 := by
  intro hcon
  refine h ?_
  have hh : ((M2 r1 r2 c j : ℤ) : ℂ) = 0 := by unfold M2; push_cast; linear_combination hcon
  exact_mod_cast hh

lemma d3C (p q j : ℕ) (h : D3g p q j ≠ 0) :
    ((YI 0 p : ℤ) : ℂ) * (((YI 1 q : ℤ) : ℂ) * ((YI 2 j : ℤ) : ℂ)
        - ((YI 2 q : ℤ) : ℂ) * ((YI 1 j : ℤ) : ℂ))
      - ((YI 0 q : ℤ) : ℂ) * (((YI 1 p : ℤ) : ℂ) * ((YI 2 j : ℤ) : ℂ)
        - ((YI 2 p : ℤ) : ℂ) * ((YI 1 j : ℤ) : ℂ))
      + ((YI 0 j : ℤ) : ℂ) * (((YI 1 p : ℤ) : ℂ) * ((YI 2 q : ℤ) : ℂ)
        - ((YI 2 p : ℤ) : ℂ) * ((YI 1 q : ℤ) : ℂ)) ≠ 0 := by
  intro hcon
  refine h ?_
  have hh : ((D3g p q j : ℤ) : ℂ) = 0 := by unfold D3g dt; push_cast; linear_combination hcon
  exact_mod_cast hh

/-- Elimination for a singleton `u`-class (`c = 8` or `c = 9`). -/
lemma killG2 (M c j0 : ℕ) (hcv : c = 8 ∨ c = 9) (hj0 : j0 < 14 + 4 * M) (R : ℕ → ℂ)
    (hs : ∀ i, i < 14 + 4 * M → i ≠ c → i ≠ j0 → R i = 0)
    (hrel : ∀ r, r < 3 → (∑ i ∈ Finset.range (14 + 4 * M), ((YI r i : ℤ) : ℂ) * R i) = 0) :
    ∀ i, i < 14 + 4 * M → R i = 0 := by
  have hclt : c < 14 + 4 * M := by rcases hcv with rfl | rfl <;> omega
  obtain ⟨jj, hjjlt, hjjne, hz⟩ : ∃ jj, jj < 14 + 4 * M ∧ c ≠ jj ∧
      (∀ i, i < 14 + 4 * M → i ≠ c → i ≠ jj → R i = 0) := by
    by_cases hjc : j0 = c
    · refine ⟨0, by omega, by rcases hcv with rfl | rfl <;> omega, ?_⟩
      intro i hi h1 _
      exact hs i hi h1 (by rw [hjc]; exact h1)
    · exact ⟨j0, hj0, fun h => hjc h.symm, fun i hi h1 h2 => hs i hi h1 h2⟩
  have e0 := expand2h (14 + 4 * M) c jj hclt hjjlt hjjne
    (fun i => ((YI 0 i : ℤ) : ℂ)) R hz (hrel 0 (by norm_num))
  have e1 := expand2h (14 + 4 * M) c jj hclt hjjlt hjjne
    (fun i => ((YI 1 i : ℤ) : ℂ)) R hz (hrel 1 (by norm_num))
  have e2 := expand2h (14 + 4 * M) c jj hclt hjjlt hjjne
    (fun i => ((YI 2 i : ℤ) : ℂ)) R hz (hrel 2 (by norm_num))
  -- (types are already beta-reduced)
  have hd := minorDet c jj hcv (fun h => hjjne h.symm)
  have hdC : ((YI 0 c : ℤ) : ℂ) * ((YI 1 jj : ℤ) : ℂ)
        - ((YI 1 c : ℤ) : ℂ) * ((YI 0 jj : ℤ) : ℂ) ≠ 0 ∨
      ((YI 0 c : ℤ) : ℂ) * ((YI 2 jj : ℤ) : ℂ)
        - ((YI 2 c : ℤ) : ℂ) * ((YI 0 jj : ℤ) : ℂ) ≠ 0 ∨
      ((YI 1 c : ℤ) : ℂ) * ((YI 2 jj : ℤ) : ℂ)
        - ((YI 2 c : ℤ) : ℂ) * ((YI 1 jj : ℤ) : ℂ) ≠ 0 := by
    rcases hd with h | h | h
    · exact Or.inl (m2C 0 1 c jj h)
    · exact Or.inr (Or.inl (m2C 0 2 c jj h))
    · exact Or.inr (Or.inr (m2C 1 2 c jj h))
  obtain ⟨x0, x1⟩ := pick2 e0 e1 e2 hdC
  intro i hi
  by_cases h1 : i = c
  · rw [h1]; exact x0
  by_cases h2 : i = jj
  · rw [h2]; exact x1
  exact hz i hi h1 h2

/-- Elimination for a two-element `u`-class. -/
lemma killG3 (M k0 j0 : ℕ) (hk0 : k0 < 8 + 2 * M) (h4 : k0 ≠ 4) (h5 : k0 ≠ 5)
    (hj0 : j0 < 14 + 4 * M) (R : ℕ → ℂ)
    (hs : ∀ i, i < 14 + 4 * M → i ≠ cp k0 → i ≠ cq k0 → i ≠ j0 → R i = 0)
    (hrel : ∀ r, r < 3 → (∑ i ∈ Finset.range (14 + 4 * M), ((YI r i : ℤ) : ℂ) * R i) = 0) :
    ∀ i, i < 14 + 4 * M → R i = 0 := by
  have hplt := cp_lt M k0 hk0
  have hqlt := cq_lt M k0 hk0
  have hpq : cp k0 ≠ cq k0 := by have := cp_lt_cq k0 h4 h5; omega
  obtain ⟨jj, hjjlt, hpj, hqj, hz⟩ : ∃ jj, jj < 14 + 4 * M ∧ cp k0 ≠ jj ∧ cq k0 ≠ jj ∧
      (∀ i, i < 14 + 4 * M → i ≠ cp k0 → i ≠ cq k0 → i ≠ jj → R i = 0) := by
    by_cases hjc : j0 = cp k0 ∨ j0 = cq k0
    · by_cases hk : k0 = 0
      · subst hk
        refine ⟨2, by omega, by rw [cp0]; omega, by rw [cq0]; omega, ?_⟩
        intro i hi a1 a2 _
        refine hs i hi a1 a2 ?_
        rcases hjc with h | h <;> rw [h] <;> assumption
      · refine ⟨0, by omega, by have := cp_pos k0 hk; omega, by have := cq_pos k0; omega, ?_⟩
        intro i hi a1 a2 _
        refine hs i hi a1 a2 ?_
        rcases hjc with h | h <;> rw [h] <;> assumption
    · push_neg at hjc
      exact ⟨j0, hj0, fun h => hjc.1 h.symm, fun h => hjc.2 h.symm,
        fun i hi a1 a2 a3 => hs i hi a1 a2 a3⟩
  have e0 := expand3h (14 + 4 * M) (cp k0) (cq k0) jj hplt hqlt hjjlt hpq hpj hqj
    (fun i => ((YI 0 i : ℤ) : ℂ)) R hz (hrel 0 (by norm_num))
  have e1 := expand3h (14 + 4 * M) (cp k0) (cq k0) jj hplt hqlt hjjlt hpq hpj hqj
    (fun i => ((YI 1 i : ℤ) : ℂ)) R hz (hrel 1 (by norm_num))
  have e2 := expand3h (14 + 4 * M) (cp k0) (cq k0) jj hplt hqlt hjjlt hpq hpj hqj
    (fun i => ((YI 2 i : ℤ) : ℂ)) R hz (hrel 2 (by norm_num))
  -- (types are already beta-reduced)
  have hdC := d3C (cp k0) (cq k0) jj
    (mainDet M k0 jj hk0 h4 h5 (fun h => hpj h.symm) (fun h => hqj h.symm))
  obtain ⟨x0, x1, x2⟩ := tri3g e0 e1 e2 hdC
  intro i hi
  by_cases h1 : i = cp k0
  · rw [h1]; exact x0
  by_cases h2 : i = cq k0
  · rw [h2]; exact x1
  by_cases h3 : i = jj
  · rw [h3]; exact x2
  exact hz i hi h1 h2 h3

/-- The general elimination step. -/
lemma killG (M k0 j0 : ℕ) (hk0 : k0 < 8 + 2 * M) (hj0 : j0 < 14 + 4 * M) (R : ℕ → ℂ)
    (hs : ∀ i, i < 14 + 4 * M → clsI i ≠ k0 → i ≠ j0 → R i = 0)
    (hrel : ∀ r, r < 3 → (∑ i ∈ Finset.range (14 + 4 * M), ((YI r i : ℤ) : ℂ) * R i) = 0) :
    ∀ i, i < 14 + 4 * M → R i = 0 := by
  by_cases h4 : k0 = 4
  · subst h4
    refine killG2 M 8 j0 (Or.inl rfl) hj0 R (fun i hi h1 h2 => hs i hi ?_ h2) hrel
    intro hcl
    rcases clsCov M i hi with h | h
    · rw [hcl, cp4] at h; exact h1 h
    · rw [hcl, cq4] at h; exact h1 h
  by_cases h5 : k0 = 5
  · subst h5
    refine killG2 M 9 j0 (Or.inr rfl) hj0 R (fun i hi h1 h2 => hs i hi ?_ h2) hrel
    intro hcl
    rcases clsCov M i hi with h | h
    · rw [hcl, cp5] at h; exact h1 h
    · rw [hcl, cq5] at h; exact h1 h
  · refine killG3 M k0 j0 hk0 h4 h5 hj0 R (fun i hi h1 h2 h3 => hs i hi ?_ h3) hrel
    intro hcl
    rcases clsCov M i hi with h | h
    · rw [hcl] at h; exact h1 h
    · rw [hcl] at h; exact h2 h


/-! ## Unextendibility for every `M` -/

lemma swapsumG (n d : ℕ) (f : ℕ → ℂ) (g : ℕ → ℕ → ℂ) (c : ℕ → ℂ) :
    (∑ i ∈ Finset.range n, f i * ∑ s ∈ Finset.range d, g i s * c s)
      = ∑ s ∈ Finset.range d, (∑ i ∈ Finset.range n, f i * g i s) * c s := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring

lemma relG (M : ℕ) (c : ℕ → ℂ) (r : ℕ) (hr : r < 3) :
    (∑ i ∈ Finset.range (14 + 4 * M), ((YI r i : ℤ) : ℂ) *
      (∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c s)) = 0 := by
  rw [swapsumG]
  refine Finset.sum_eq_zero fun s hs => ?_
  have h : (∑ i ∈ Finset.range (14 + 4 * M), ((YI r i : ℤ) : ℂ) * ((ZG i s : ℤ) : ℂ))
      = ((∑ i ∈ Finset.range (14 + 4 * M), YI r i * ZG i s : ℤ) : ℂ) := by push_cast; ring
  rw [h, YZ M r s hr (Finset.mem_range.mp hs)]
  simp

theorem unextGen (M : ℕ) (a b c : ℕ → ℂ)
    (ha : ¬ (a 0 = 0 ∧ a 1 = 0)) (hb : ¬ (b 0 = 0 ∧ b 1 = 0))
    (hc : ∃ s, s < 11 + 4 * M ∧ c s ≠ 0) :
    ∃ i, i < 14 + 4 * M ∧
      (((UI i 0 : ℤ) : ℂ) * a 0 + ((UI i 1 : ℤ) : ℂ) * a 1) *
      (((WI M i 0 : ℤ) : ℂ) * b 0 + ((WI M i 1 : ℤ) : ℂ) * b 1) *
      (∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c s) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have huniqU : ∀ i i', clsI i ≠ clsI i' →
      (((UI i 0 : ℤ) : ℂ) * a 0 + ((UI i 1 : ℤ) : ℂ) * a 1) = 0 →
      (((UI i' 0 : ℤ) : ℂ) * a 0 + ((UI i' 1 : ℤ) : ℂ) * a 1) = 0 → False := by
    intro i i' hne e1 e2
    have hd : ((UI i 0 : ℤ) : ℂ) * ((UI i' 1 : ℤ) : ℂ)
        - ((UI i' 0 : ℤ) : ℂ) * ((UI i 1 : ℤ) : ℂ) ≠ 0 := by
      intro h0
      refine detU i i' hne ?_
      have hh : ((UI i 0 * UI i' 1 - UI i' 0 * UI i 1 : ℤ) : ℂ) = 0 := by
        push_cast; linear_combination h0
      exact_mod_cast hh
    obtain ⟨p0, p1⟩ := tri2g e1 e2 hd
    exact ha ⟨p0, p1⟩
  obtain ⟨k0, hk0lt, hk0⟩ : ∃ k0, k0 < 8 + 2 * M ∧ ∀ i, i < 14 + 4 * M →
      (((UI i 0 : ℤ) : ℂ) * a 0 + ((UI i 1 : ℤ) : ℂ) * a 1) = 0 → clsI i = k0 := by
    by_cases h : ∃ i, i < 14 + 4 * M ∧
        (((UI i 0 : ℤ) : ℂ) * a 0 + ((UI i 1 : ℤ) : ℂ) * a 1) = 0
    · obtain ⟨i0, hi0, he0⟩ := h
      refine ⟨clsI i0, clsI_lt M i0 hi0, ?_⟩
      intro i hi hei
      by_contra hne
      exact huniqU i i0 hne hei he0
    · push_neg at h
      exact ⟨0, by omega, fun i hi hei => absurd hei (h i hi)⟩
  have huniqW : ∀ i i', i < 14 + 4 * M → i' < 14 + 4 * M → i ≠ i' →
      (((WI M i 0 : ℤ) : ℂ) * b 0 + ((WI M i 1 : ℤ) : ℂ) * b 1) = 0 →
      (((WI M i' 0 : ℤ) : ℂ) * b 0 + ((WI M i' 1 : ℤ) : ℂ) * b 1) = 0 → False := by
    intro i i' hi hi' hne e1 e2
    have hd : ((WI M i 0 : ℤ) : ℂ) * ((WI M i' 1 : ℤ) : ℂ)
        - ((WI M i' 0 : ℤ) : ℂ) * ((WI M i 1 : ℤ) : ℂ) ≠ 0 := by
      intro h0
      refine detWAll M i i' hi hi' hne ?_
      have hh : ((WI M i 0 * WI M i' 1 - WI M i' 0 * WI M i 1 : ℤ) : ℂ) = 0 := by
        push_cast; linear_combination h0
      exact_mod_cast hh
    obtain ⟨p0, p1⟩ := tri2g e1 e2 hd
    exact hb ⟨p0, p1⟩
  obtain ⟨j0, hj0lt, hj0⟩ : ∃ j0, j0 < 14 + 4 * M ∧ ∀ i, i < 14 + 4 * M →
      (((WI M i 0 : ℤ) : ℂ) * b 0 + ((WI M i 1 : ℤ) : ℂ) * b 1) = 0 → i = j0 := by
    by_cases h : ∃ i, i < 14 + 4 * M ∧
        (((WI M i 0 : ℤ) : ℂ) * b 0 + ((WI M i 1 : ℤ) : ℂ) * b 1) = 0
    · obtain ⟨i0, hi0, he0⟩ := h
      refine ⟨i0, hi0, ?_⟩
      intro i hi hei
      by_contra hne
      exact huniqW i i0 hi hi0 hne hei he0
    · push_neg at h
      exact ⟨0, by omega, fun i hi hei => absurd hei (h i hi)⟩
  have hsupp : ∀ i, i < 14 + 4 * M → clsI i ≠ k0 → i ≠ j0 →
      (∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c s) = 0 := by
    intro i hi h1 h2
    have hz := hcon i hi
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (hk0 i hi h') h1
      · exact absurd (hj0 i hi h') h2
    · exact h
  have hall := killG M k0 j0 hk0lt hj0lt
    (fun i => ∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c s) hsupp
    (fun r hr => relG M c r hr)
  obtain ⟨s, hs, hcs⟩ := hc
  exact hcs (injAll M c (fun i hi => hall i hi) s hs)


/-! ## Orthogonality for every `M`, including `M = 0` -/

lemma orth0dec : ∀ i ∈ Finset.range 14, ∀ j ∈ Finset.range 14, i ≠ j →
    ipu i j * ipw 0 i j * (∑ s ∈ Finset.range 11, ZG i s * ZG j s) = 0 := by decide

lemma orthAll (M i j : ℕ) (hi : i < 14 + 4 * M) (hj : j < 14 + 4 * M) (hij : i ≠ j) :
    ipu i j * ipw M i j * (∑ s ∈ Finset.range (11 + 4 * M), ZG i s * ZG j s) = 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have h := orth0dec i (Finset.mem_range.mpr (by omega)) j (Finset.mem_range.mpr (by omega)) hij
    simpa using h
  · exact orthGen M hM i j hi hj hij

/-! ## Bridges to `Fin`-indexed sums -/

lemma ipuC (a b : ℕ) :
    (∑ r : Fin 2, star (((UI a r.val : ℤ) : ℂ)) * ((UI b r.val : ℤ) : ℂ))
      = ((ipu a b : ℤ) : ℂ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, ipu, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.val_one, add_zero]
  push_cast
  ring

lemma ipwC (M a b : ℕ) :
    (∑ r : Fin 2, star (((WI M a r.val : ℤ) : ℂ)) * ((WI M b r.val : ℤ) : ℂ))
      = ((ipw M a b : ℤ) : ℂ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, ipw, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.val_one, add_zero]
  push_cast
  ring

lemma ipzC (M a b : ℕ) :
    (∑ r : Fin (11 + 4 * M), star (((ZG a r.val : ℤ) : ℂ)) * ((ZG b r.val : ℤ) : ℂ))
      = ((∑ s ∈ Finset.range (11 + 4 * M), ZG a s * ZG b s : ℤ) : ℂ) := by
  simp only [star_intCast]
  rw [Fin.sum_univ_eq_sum_range (fun s => ((ZG a s : ℤ) : ℂ) * ((ZG b s : ℤ) : ℂ))]
  push_cast
  rfl

lemma pair2C (f : ℕ → ℤ) (a : Fin 2 → ℂ) (a' : ℕ → ℂ) (h0 : a' 0 = a 0) (h1 : a' 1 = a 1) :
    (∑ r : Fin 2, star ((f r.val : ℤ) : ℂ) * a r)
      = ((f 0 : ℤ) : ℂ) * a' 0 + ((f 1 : ℤ) : ℂ) * a' 1 := by
  rw [h0, h1]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.val_one, add_zero]

lemma sumZC (M i : ℕ) (c : Fin (11 + 4 * M) → ℂ) (c' : ℕ → ℂ)
    (hcc : ∀ s : Fin (11 + 4 * M), c' s.val = c s) :
    (∑ r : Fin (11 + 4 * M), star ((ZG i r.val : ℤ) : ℂ) * c r)
      = ∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) * c' s := by
  rw [← Fin.sum_univ_eq_sum_range (fun s => ((ZG i s : ℤ) : ℂ) * c' s)]
  exact Finset.sum_congr rfl fun r _ => by rw [hcc r]; simp only [star_intCast]

/-! ## The family is an unextendible product basis, for every `M` -/

theorem familyGen (M : ℕ)
    (u : Fin (14 + 4 * M) → Fin 2 → ℂ) (w : Fin (14 + 4 * M) → Fin 2 → ℂ)
    (z : Fin (14 + 4 * M) → Fin (11 + 4 * M) → ℂ)
    (hu : u = (fun i r => ((UI i.val r.val : ℤ) : ℂ)))
    (hw : w = (fun i r => ((WI M i.val r.val : ℤ) : ℂ)))
    (hzz : z = (fun i r => ((ZG i.val r.val : ℤ) : ℂ))) :
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
        (∑ r, star (z i r) * c r) ≠ 0) := by
  subst hu; subst hw; subst hzz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hcon
    rcases UI_nz i.val with h | h
    · exact h (by have := congrFun hcon 0; simpa using this)
    · exact h (by have := congrFun hcon 1; simpa using this)
  · intro i hcon
    rcases WI_nz M i.val with h | h
    · exact h (by have := congrFun hcon 0; simpa using this)
    · exact h (by have := congrFun hcon 1; simpa using this)
  · intro i hcon
    obtain ⟨s, hs, hne⟩ := ZG_nz M i.val i.isLt
    exact hne (by have := congrFun hcon ⟨s, hs⟩; simpa using this)
  · intro i j hij
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [ipuC i.val j.val, ipwC M i.val j.val, ipzC M i.val j.val,
        ← Int.cast_mul, ← Int.cast_mul, orthAll M i.val j.val i.isLt j.isLt hv,
        Int.cast_zero]
  · intro a ha b hb c hc
    refine ?_
    have ha' : ¬ ((fun n => if h : n < 2 then a ⟨n, h⟩ else 0) 0 = 0 ∧
        (fun n => if h : n < 2 then a ⟨n, h⟩ else 0) 1 = 0) := by
      rintro ⟨h0, h1⟩
      refine ha ?_
      funext r
      fin_cases r
      · simpa using h0
      · simpa using h1
    have hb' : ¬ ((fun n => if h : n < 2 then b ⟨n, h⟩ else 0) 0 = 0 ∧
        (fun n => if h : n < 2 then b ⟨n, h⟩ else 0) 1 = 0) := by
      rintro ⟨h0, h1⟩
      refine hb ?_
      funext r
      fin_cases r
      · simpa using h0
      · simpa using h1
    have hc' : ∃ s, s < 11 + 4 * M ∧
        (fun n => if h : n < 11 + 4 * M then c ⟨n, h⟩ else 0) s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hc ?_
      funext s
      have h := hcon s.val s.isLt
      simpa using h
    obtain ⟨i, hi, hne⟩ := unextGen M (fun n => if h : n < 2 then a ⟨n, h⟩ else 0)
      (fun n => if h : n < 2 then b ⟨n, h⟩ else 0)
      (fun n => if h : n < 11 + 4 * M then c ⟨n, h⟩ else 0) ha' hb' hc'
    refine ⟨⟨i, hi⟩, ?_⟩
    have e1 : (∑ r : Fin 2, star (((UI i r.val : ℤ) : ℂ)) * a r)
        = ((UI i 0 : ℤ) : ℂ) * (fun n => if h : n < 2 then a ⟨n, h⟩ else 0) 0
          + ((UI i 1 : ℤ) : ℂ) * (fun n => if h : n < 2 then a ⟨n, h⟩ else 0) 1 :=
      pair2C (fun r => UI i r) a (fun n => if h : n < 2 then a ⟨n, h⟩ else 0)
        (by norm_num) (by norm_num)
    have e2 : (∑ r : Fin 2, star (((WI M i r.val : ℤ) : ℂ)) * b r)
        = ((WI M i 0 : ℤ) : ℂ) * (fun n => if h : n < 2 then b ⟨n, h⟩ else 0) 0
          + ((WI M i 1 : ℤ) : ℂ) * (fun n => if h : n < 2 then b ⟨n, h⟩ else 0) 1 :=
      pair2C (fun r => WI M i r) b (fun n => if h : n < 2 then b ⟨n, h⟩ else 0)
        (by norm_num) (by norm_num)
    have e3 : (∑ r : Fin (11 + 4 * M), star (((ZG i r.val : ℤ) : ℂ)) * c r)
        = ∑ s ∈ Finset.range (11 + 4 * M), ((ZG i s : ℤ) : ℂ) *
            (fun n => if h : n < 11 + 4 * M then c ⟨n, h⟩ else 0) s :=
      sumZC M i c (fun n => if h : n < 11 + 4 * M then c ⟨n, h⟩ else 0) (fun s => by simp)
    dsimp only
    rw [e1, e2, e3]
    exact hne


/-- The statement's `M`-indexed third factor. It is definitionally the `M`-free `ZG`. -/
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

lemma ZI_eq (M i s : ℕ) : ZI M i s = ZG i s := rfl

/-- For every `M`, the explicit family `(UI, WI M, ZI M)` is an unextendible product basis
of cardinality `14 + 4M` in `C² ⊗ C² ⊗ C^(11 + 4M)`; that is the `k = M + 3` case of
`MinUPB224kMinus1`. -/
theorem proof :
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
            (∑ r, star (z i r) * c r) ≠ 0) := by
  intro M u w z hu hw hz
  exact familyGen M u w z hu hw hz

end Submissions.UPBCyclicFamily224k.Cyclic
