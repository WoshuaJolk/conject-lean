import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The cyclic family is an orthogonal product set, for every `M ≥ 1`

Proof outline. `ZI` does not mention `M`, so the family is one infinite configuration cut off
in two places; every inner product is `M`-independent. Write `d = 11 + 4M` and split a third
factor into an 11-coordinate base part and `M` windows of 4. Then

  `⟨zᵢ, zⱼ⟩ = Σ_{s<11} Zb i s · Zb j s + Σ_{m<M} EIP i j m`,

which is `ipz_split`. `EIP i j m` vanishes unless the windows of `i` and `j` both meet window
`m`, and the window structure is: states `1` and `2` meet every window; `10` and `12` meet
window `0`; the `A`/`C` of block `mm` meet windows `mm` and `mm+1`; the `B`/`D` of block `mm`
meet window `mm` only.

For each pair one of the three factors vanishes:

* a `u`-parallel class handles two states of the same block in orthogonal classes;
* a `w`-parallel class handles the seven matched pairs among the base, the two long edges
  `(1, A_{M-1})` and `(2, C_{M-1})`, and the inter-block edges `(A_m, D_{m+1})`,
  `(C_m, B_{m+1})`;
* everything else has `⟨zᵢ, zⱼ⟩ = 0`, either termwise or by the two-window cancellation
  `⟨ε_A, ε*_A⟩ + ⟨ε_A, ε_D⟩ = 1 + (−1) = 0` and `⟨ε_C, ε*_C⟩ + ⟨ε_C, ε_B⟩ = 1 + (−1) = 0`.

All of that is `orthGen`. The remaining work is the passage from `Fin`-indexed sums over `ℂ`
to `Finset.range` sums over `ℤ`, which is `Fin.sum_univ_eq_sum_range` together with the fact
that `star` is inert on integer casts.
-/

namespace Submissions.UPBCyclicFamilyOrth224k.Windows



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

lemma ZI_win' (i m t : ℕ) (ht : t < 4) : ZG i (11 + 4 * m + t) = EW i m t := by
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
    rw [ZI_win' _ mm tt htt, EW_new mm tt mm tt htt]
    simp [dual_diag tt htt]



lemma ZI_eq (M i s : ℕ) : ZI M i s = ZG i s := rfl

lemma ipuC (a b : ℕ) :
    (∑ r : Fin 2, star (((UI a r.val : ℤ) : ℂ)) * ((UI b r.val : ℤ) : ℂ)) = ((ipu a b : ℤ) : ℂ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, ipu, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.val_one, add_zero]
  push_cast
  ring

lemma ipwC (M a b : ℕ) :
    (∑ r : Fin 2, star (((WI M a r.val : ℤ) : ℂ)) * ((WI M b r.val : ℤ) : ℂ)) = ((ipw M a b : ℤ) : ℂ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, star_intCast, ipw, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.val_one, add_zero]
  push_cast
  ring

lemma ipzC (M a b : ℕ) :
    (∑ r : Fin (11 + 4 * M), star (((ZI M a r.val : ℤ) : ℂ)) * ((ZI M b r.val : ℤ) : ℂ))
      = ((∑ s ∈ Finset.range (11 + 4 * M), ZG a s * ZG b s : ℤ) : ℂ) := by
  simp only [ZI_eq, star_intCast]
  rw [Fin.sum_univ_eq_sum_range (fun s => ((ZG a s : ℤ) : ℂ) * ((ZG b s : ℤ) : ℂ))]
  push_cast
  rfl

theorem proof :
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
          (∑ r, star (z i r) * z j r) = 0) := by
  intro M hM u w z hu hw hz
  subst hu; subst hw; subst hz
  refine ⟨?_, ?_, ?_, ?_⟩
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
    refine hne ?_
    have := congrFun hcon ⟨s, hs⟩
    simpa [ZI_eq] using this
  · intro i j hij
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [ipuC i.val j.val, ipwC M i.val j.val, ipzC M i.val j.val,
        ← Int.cast_mul, ← Int.cast_mul, orthGen M hM i.val j.val i.isLt j.isLt hv,
        Int.cast_zero]

end Submissions.UPBCyclicFamilyOrth224k.Windows
