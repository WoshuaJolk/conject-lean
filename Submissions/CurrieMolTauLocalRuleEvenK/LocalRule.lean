import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

/-!
# CurrieMolTauLocalRuleEvenK — `τ(f_k(1))` has a description with no `k` in it

Every result on Currie–Mol's Conjecture 1 above `k = 21` so far has been obtained one `k` at a
time, because the object the Moulin-Ollagnier descent needs to understand,

    τ(f_k(1)) = ρ^α · (k-1,k) · ρ^β · (k-1,k),

is a product whose length grows with `k`. This statement removes that growth for one explicit
family. In the cycle coordinates of `Statements.RhoCycleStructureEvenK` — `eC` on
`C₁ = {1} ∪ evens` (length `k/2+1`) and `oC` on `C₂ = {3,…,k-1}` (length `k/2-1`) —
`τ(f_k(1))` is given, for EVERY even `k ≥ 20` at once, by a rule whose only `k`-dependence is
the two block lengths:

* on `C₁`: coordinate `↦` coordinate `+ 2`, cyclically;
* on `C₂`: coordinate `↦` coordinate `+ 4`, cyclically;
* except at four letters, where it crosses between the blocks:
  `C₁` coordinate `k/2` (the letter `k`) `↦` `C₂` coordinate `3`;
  `C₁` coordinate `5` `↦` `C₂` coordinate `7`;
  `C₂` coordinate `k/2-2` (the letter `k-1`) `↦` `C₁` coordinate `1`;
  `C₂` coordinate `3` `↦` `C₁` coordinate `7`.

The four exceptional coordinates and the four landing coordinates are absolute constants. The
two exceptional sources are exactly `k` and `k-1` — the pair that `τ(1)⁻¹τ(2)` transposes —
and one fixed coordinate in each block.

The morphism is `f_k(1) = 1⁷ 2 1^{(k-12)/2} 2`, the family that the constructions at
`https://jig.so/p/3?s=13` follow at `k ≡ 0 (mod 4)`. `τ` is spelled with Currie–Mol's
`g(1) = 31`, `g(2) = 12` through `τ(1) = ρ` and `τ(2) = ρ ∘ (k-1,k)`, the last letter of a word
acting first, and `ρ` is spelled character for character as in `Statements.TauNormalForm`. The
cyclic advance is written mod-free as two guarded cases, as in `Statements.RhoCycleStructure`,
because the modulus is a variable.

## What this is for, and what it is not

The Moulin-Ollagnier algebraic property at even `k` amounts to: `τ(f_k(1))` has the same cycle
type as `ρ`, namely `(k/2+1, k/2-1)`, with `k` and `k-1` in different cycles. Establishing that
symbolically in `k` — as opposed to recomputing it for each `k` — needs a description of
`τ(f_k(1))` that does not grow with `k`, and this is that description. The cycle-type
conclusion itself is NOT proved here; it needs an orbit argument on top of this rule, and that
argument is not formalised.

Two things this does not do, stated because they bound the route. First, it settles no case of
the conjecture: the algebraic property is one hypothesis of Currie–Mol's Theorem 5, and the
freeness of the decoded word is a separate matter — for this family the decoded word was
checked in the session that produced this statement and is NOT undirected `((k-1)/(k-2))⁺`-free
at `k = 64`, the first failure being at position 19 854, so the family does not give an
infinite sequence of constructions and no `k`-uniform algebraic property could make it. Second,
an exhaustive scan over `α, β ≤ 30` against every even `k` in `[20, 80]` found no pair of
CONSTANTS that works for all `k`, so a family whose morphism length does not grow with `k` does
not exist in this shape. What is uniform here is the description, not the morphism.
-/

namespace Submissions.CurrieMolTauLocalRuleEvenK.LocalRule

def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2
def tt (k j : ℕ) : ℕ := if j = k - 1 then k else if j = k then k - 1 else j
def tauL (k c j : ℕ) : ℕ := if c = 1 then rho k j else rho k (tt k j)
def tauW (k : ℕ) (u : List ℕ) (j : ℕ) : ℕ := u.foldr (tauL k) j
def fOne (k : ℕ) : List ℕ := List.replicate 7 1 ++ (2 :: (List.replicate ((k - 12) / 2) 1 ++ [2]))
def inC1 (k j : ℕ) : Prop := j = 1 ∨ (2 ≤ j ∧ j ≤ k ∧ j % 2 = 0)
def inC2 (k j : ℕ) : Prop := 3 ≤ j ∧ j + 1 ≤ k ∧ j % 2 = 1
def eC (j : ℕ) : ℕ := if j = 1 then 0 else j / 2
def oC (j : ℕ) : ℕ := (j - 3) / 2

variable {k : ℕ}

theorem rho_C1 (hk : 6 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j) : inC1 k (rho k j) := by
  unfold inC1 at h ⊢; unfold rho; split_ifs <;> omega
theorem rho_C2 (hk : 6 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j) : inC2 k (rho k j) := by
  unfold inC2 at h ⊢; unfold rho; split_ifs <;> omega
theorem eC_step (hk : 6 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j) (hlt : eC j < k / 2) :
    eC (rho k j) = eC j + 1 := by
  unfold inC1 at h; unfold eC at hlt ⊢; unfold rho; split_ifs at hlt ⊢ <;> omega
theorem oC_step (hk : 6 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j) (hlt : oC j + 2 < k / 2) :
    oC (rho k j) = oC j + 1 := by
  unfold inC2 at h; unfold oC at hlt ⊢; unfold rho; split_ifs <;> omega
theorem eC_wrap (hk : 6 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j) (he : eC j = k / 2) :
    eC (rho k j) = 0 ∧ inC1 k (rho k j) := by
  refine ⟨?_, rho_C1 hk hke h⟩
  unfold inC1 at h; unfold eC at he ⊢; unfold rho; split_ifs at he ⊢ <;> omega
theorem oC_wrap (hk : 6 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j) (he : oC j + 2 = k / 2) :
    oC (rho k j) = 0 ∧ inC2 k (rho k j) := by
  refine ⟨?_, rho_C2 hk hke h⟩
  unfold inC2 at h; unfold oC at he ⊢; unfold rho; split_ifs at he ⊢ <;> omega

theorem eC_iter (hk : 6 ≤ k) (hke : k % 2 = 0) :
    ∀ (n : ℕ) {j : ℕ}, inC1 k j → eC j + n ≤ k / 2 →
      inC1 k ((rho k)^[n] j) ∧ eC ((rho k)^[n] j) = eC j + n := by
  intro n
  induction n with
  | zero => intro j h _; simpa using h
  | succ n ih =>
      intro j h hb
      have h1 : inC1 k (rho k j) := rho_C1 hk hke h
      have h2 : eC (rho k j) = eC j + 1 := eC_step hk hke h (by omega)
      have := ih h1 (by omega)
      rw [Function.iterate_succ_apply]
      exact ⟨this.1, by rw [this.2, h2]; omega⟩

theorem oC_iter (hk : 6 ≤ k) (hke : k % 2 = 0) :
    ∀ (n : ℕ) {j : ℕ}, inC2 k j → oC j + n + 2 ≤ k / 2 →
      inC2 k ((rho k)^[n] j) ∧ oC ((rho k)^[n] j) = oC j + n := by
  intro n
  induction n with
  | zero => intro j h _; simpa using h
  | succ n ih =>
      intro j h hb
      have h1 : inC2 k (rho k j) := rho_C2 hk hke h
      have h2 : oC (rho k j) = oC j + 1 := oC_step hk hke h (by omega)
      have := ih h1 (by omega)
      rw [Function.iterate_succ_apply]
      exact ⟨this.1, by rw [this.2, h2]; omega⟩

theorem eC_iter_wrap (hk : 6 ≤ k) (hke : k % 2 = 0) (n : ℕ) {j : ℕ} (h : inC1 k j)
    (h1 : k / 2 < eC j + n) (h2 : eC j + n ≤ 2 * (k / 2)) :
    inC1 k ((rho k)^[n] j) ∧ eC ((rho k)^[n] j) = eC j + n - (k / 2 + 1) := by
  have hb : eC j ≤ k / 2 := by unfold inC1 at h; unfold eC; split_ifs <;> omega
  set s := k / 2 - eC j with hs
  have hstep : inC1 k ((rho k)^[s] j) ∧ eC ((rho k)^[s] j) = eC j + s :=
    eC_iter hk hke s h (by omega)
  have htop : eC ((rho k)^[s] j) = k / 2 := by rw [hstep.2]; omega
  have hw := eC_wrap hk hke hstep.1 htop
  set t := n - s - 1 with ht
  have hsplit : (rho k)^[n] j = (rho k)^[t] ((rho k)^[s + 1] j) := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  have hone : (rho k)^[s + 1] j = rho k ((rho k)^[s] j) := by rw [Function.iterate_succ_apply']
  have hfin : inC1 k ((rho k)^[t] ((rho k)^[s+1] j)) ∧
      eC ((rho k)^[t] ((rho k)^[s+1] j)) = eC ((rho k)^[s+1] j) + t := by
    refine eC_iter hk hke t ?_ ?_
    · rw [hone]; exact hw.2
    · rw [hone, hw.1]; omega
  rw [hsplit]; refine ⟨hfin.1, ?_⟩; rw [hfin.2, hone, hw.1]; omega

theorem oC_iter_wrap (hk : 6 ≤ k) (hke : k % 2 = 0) (n : ℕ) {j : ℕ} (h : inC2 k j)
    (h1 : k / 2 < oC j + n + 2) (h2 : oC j + n + 2 ≤ 2 * (k / 2) - 2) :
    inC2 k ((rho k)^[n] j) ∧ oC ((rho k)^[n] j) + 2 = oC j + n + 2 - (k / 2 - 1) := by
  have hb : oC j + 2 ≤ k / 2 := by unfold inC2 at h; unfold oC; omega
  set s := k / 2 - 2 - oC j with hs
  have hstep : inC2 k ((rho k)^[s] j) ∧ oC ((rho k)^[s] j) = oC j + s :=
    oC_iter hk hke s h (by omega)
  have htop : oC ((rho k)^[s] j) + 2 = k / 2 := by rw [hstep.2]; omega
  have hw := oC_wrap hk hke hstep.1 htop
  set t := n - s - 1 with ht
  have hsplit : (rho k)^[n] j = (rho k)^[t] ((rho k)^[s + 1] j) := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  have hone : (rho k)^[s + 1] j = rho k ((rho k)^[s] j) := by rw [Function.iterate_succ_apply']
  have hfin : inC2 k ((rho k)^[t] ((rho k)^[s+1] j)) ∧
      oC ((rho k)^[t] ((rho k)^[s+1] j)) = oC ((rho k)^[s+1] j) + t := by
    refine oC_iter hk hke t ?_ ?_
    · rw [hone]; exact hw.2
    · rw [hone, hw.1]; omega
  rw [hsplit]; refine ⟨hfin.1, ?_⟩; rw [hfin.2, hone, hw.1]; omega

theorem tt_C1_id (hk : 6 ≤ k) (hke : k % 2 = 0) {x : ℕ} (h : inC1 k x) (hne : eC x ≠ k / 2) :
    tt k x = x := by
  unfold inC1 at h; unfold eC at hne; unfold tt; split_ifs at hne ⊢ <;> omega
theorem tt_C1_top (hk : 6 ≤ k) (hke : k % 2 = 0) {x : ℕ} (h : inC1 k x) (he : eC x = k / 2) :
    tt k x = k - 1 := by
  unfold inC1 at h; unfold eC at he; unfold tt; split_ifs at he ⊢ <;> omega
theorem tt_C2_id (hk : 6 ≤ k) (hke : k % 2 = 0) {x : ℕ} (h : inC2 k x) (hne : oC x + 2 ≠ k / 2) :
    tt k x = x := by
  unfold inC2 at h; unfold oC at hne; unfold tt; split_ifs <;> omega
theorem tt_C2_top (hk : 6 ≤ k) (hke : k % 2 = 0) {x : ℕ} (h : inC2 k x) (he : oC x + 2 = k / 2) :
    tt k x = k := by
  unfold inC2 at h; unfold oC at he; unfold tt; split_ifs <;> omega

theorem tauW_rep (n : ℕ) : ∀ j : ℕ, tauW k (List.replicate n 1) j = (rho k)^[n] j := by
  induction n with
  | zero => intro j; simp [tauW]
  | succ n ih =>
      intro j
      have h : tauW k (List.replicate (n+1) 1) j = rho k (tauW k (List.replicate n 1) j) := by
        simp [tauW, List.replicate_succ, tauL]
      rw [h, ih j]
      exact (Function.iterate_succ_apply' (rho k) n j).symm

theorem tauW_append (u v : List ℕ) (j : ℕ) : tauW k (u ++ v) j = tauW k u (tauW k v j) := by
  simp [tauW, List.foldr_append]

theorem tauW_fOne (hk : 12 ≤ k) (hke : k % 2 = 0) (j : ℕ) :
    tauW k (fOne k) j = (rho k)^[8] (tt k ((rho k)^[(k - 10) / 2] (tt k j))) := by
  have h2 : tauW k [2] j = rho k (tt k j) := by simp [tauW, tauL]
  have hm : tauW k (List.replicate ((k-12)/2) 1 ++ [2]) j
      = (rho k)^[(k-12)/2] (rho k (tt k j)) := by rw [tauW_append, tauW_rep, h2]
  have hmid : tauW k (2 :: (List.replicate ((k-12)/2) 1 ++ [2])) j
      = rho k (tt k ((rho k)^[(k-12)/2] (rho k (tt k j)))) := by
    show tauL k 2 (tauW k (List.replicate ((k-12)/2) 1 ++ [2]) j) = _
    rw [hm]; simp [tauL]
  have hall : tauW k (fOne k) j
      = (rho k)^[7] (rho k (tt k ((rho k)^[(k-12)/2] (rho k (tt k j))))) := by
    unfold fOne; rw [tauW_append, hmid, tauW_rep]
  have e1 : (rho k)^[(k-12)/2] (rho k (tt k j)) = (rho k)^[(k-12)/2 + 1] (tt k j) :=
    (Function.iterate_succ_apply (rho k) ((k-12)/2) (tt k j)).symm
  have e1' : (k-12)/2 + 1 = (k-10)/2 := by omega
  rw [hall, e1, e1']
  exact (Function.iterate_succ_apply (rho k) 7 _).symm


theorem loc1 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j) (he : eC j = k / 2) :
    inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = 3 := by
  rw [tauW_fOne (by omega) hke, tt_C1_top (by omega) hke h he]
  have hc2 : inC2 k (k - 1) := by unfold inC2; omega
  have ho : oC (k - 1) = k / 2 - 2 := by unfold oC; omega
  have s1 := oC_iter_wrap (k := k) (by omega) hke ((k-10)/2) hc2 (by rw [ho]; omega)
    (by rw [ho]; omega)
  set x := (rho k)^[(k-10)/2] (k - 1) with hx
  have hox : oC x = k / 2 - 6 := by have h2 := s1.2; rw [ho] at h2; omega
  rw [tt_C2_id (by omega) hke s1.1 (by omega)]
  have s2 := oC_iter_wrap (k := k) (by omega) hke 8 s1.1 (by omega) (by omega)
  exact ⟨s2.1, by have h2 := s2.2; omega⟩

theorem loc2 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j) (he : eC j = 5) :
    inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = 7 := by
  rw [tauW_fOne (by omega) hke, tt_C1_id (by omega) hke h (by omega)]
  have s1 := eC_iter (k := k) (by omega) hke ((k-10)/2) h (by omega)
  set x := (rho k)^[(k-10)/2] j with hx
  have hex : eC x = k / 2 := by have h2 := s1.2; omega
  rw [tt_C1_top (by omega) hke s1.1 hex]
  have hc2 : inC2 k (k - 1) := by unfold inC2; omega
  have ho : oC (k - 1) = k / 2 - 2 := by unfold oC; omega
  have s2 := oC_iter_wrap (k := k) (by omega) hke 8 hc2 (by rw [ho]; omega) (by rw [ho]; omega)
  exact ⟨s2.1, by have h2 := s2.2; rw [ho] at h2; omega⟩

theorem loc3 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j)
    (h1 : eC j ≠ k / 2) (h2 : eC j ≠ 5) (h3 : eC j + 2 ≤ k / 2) :
    inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = eC j + 2 := by
  have hb : eC j ≤ k / 2 := by unfold inC1 at h; unfold eC; split_ifs <;> omega
  rw [tauW_fOne (by omega) hke, tt_C1_id (by omega) hke h h1]
  by_cases hu : eC j ≤ 4
  · have s1 := eC_iter (k := k) (by omega) hke ((k-10)/2) h (by omega)
    set x := (rho k)^[(k-10)/2] j with hx
    have hex : eC x = eC j + (k-10)/2 := s1.2
    rw [tt_C1_id (by omega) hke s1.1 (by omega)]
    have s2 := eC_iter_wrap (k := k) (by omega) hke 8 s1.1 (by omega) (by omega)
    exact ⟨s2.1, by have h4 := s2.2; omega⟩
  · have s1 := eC_iter_wrap (k := k) (by omega) hke ((k-10)/2) h (by omega) (by omega)
    set x := (rho k)^[(k-10)/2] j with hx
    have hex : eC x = eC j + (k-10)/2 - (k/2+1) := s1.2
    rw [tt_C1_id (by omega) hke s1.1 (by omega)]
    have s2 := eC_iter (k := k) (by omega) hke 8 s1.1 (by omega)
    exact ⟨s2.1, by have h4 := s2.2; omega⟩

theorem loc4 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC1 k j)
    (h1 : eC j ≠ k / 2) (h2 : eC j ≠ 5) (h3 : k / 2 < eC j + 2) :
    inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = eC j + 2 - (k / 2 + 1) := by
  have hb : eC j ≤ k / 2 := by unfold inC1 at h; unfold eC; split_ifs <;> omega
  rw [tauW_fOne (by omega) hke, tt_C1_id (by omega) hke h h1]
  have s1 := eC_iter_wrap (k := k) (by omega) hke ((k-10)/2) h (by omega) (by omega)
  set x := (rho k)^[(k-10)/2] j with hx
  have hex : eC x = eC j + (k-10)/2 - (k/2+1) := s1.2
  rw [tt_C1_id (by omega) hke s1.1 (by omega)]
  have s2 := eC_iter_wrap (k := k) (by omega) hke 8 s1.1 (by omega) (by omega)
  exact ⟨s2.1, by have h4 := s2.2; omega⟩

theorem loc5 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j) (he : oC j + 2 = k / 2) :
    inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = 1 := by
  rw [tauW_fOne (by omega) hke, tt_C2_top (by omega) hke h he]
  have hc1 : inC1 k k := by unfold inC1; omega
  have hek : eC k = k / 2 := by unfold eC; split_ifs <;> omega
  have s1 := eC_iter_wrap (k := k) (by omega) hke ((k-10)/2) hc1 (by rw [hek]; omega)
    (by rw [hek]; omega)
  set x := (rho k)^[(k-10)/2] k with hx
  have hex : eC x = k / 2 - 6 := by have h2 := s1.2; rw [hek] at h2; omega
  rw [tt_C1_id (by omega) hke s1.1 (by omega)]
  have s2 := eC_iter_wrap (k := k) (by omega) hke 8 s1.1 (by omega) (by omega)
  exact ⟨s2.1, by have h2 := s2.2; omega⟩

theorem loc6 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j) (he : oC j = 3) :
    inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = 7 := by
  rw [tauW_fOne (by omega) hke, tt_C2_id (by omega) hke h (by omega)]
  have s1 := oC_iter (k := k) (by omega) hke ((k-10)/2) h (by omega)
  set x := (rho k)^[(k-10)/2] j with hx
  have hox : oC x = k / 2 - 2 := by have h2 := s1.2; omega
  rw [tt_C2_top (by omega) hke s1.1 (by omega)]
  have hc1 : inC1 k k := by unfold inC1; omega
  have hek : eC k = k / 2 := by unfold eC; split_ifs <;> omega
  have s2 := eC_iter_wrap (k := k) (by omega) hke 8 hc1 (by rw [hek]; omega) (by rw [hek]; omega)
  exact ⟨s2.1, by have h2 := s2.2; rw [hek] at h2; omega⟩

theorem loc7 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j)
    (h1 : oC j + 2 ≠ k / 2) (h2 : oC j ≠ 3) (h3 : oC j + 6 ≤ k / 2) :
    inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = oC j + 4 := by
  have hb : oC j + 2 ≤ k / 2 := by unfold inC2 at h; unfold oC; omega
  rw [tauW_fOne (by omega) hke, tt_C2_id (by omega) hke h h1]
  by_cases hv : oC j ≤ 2
  · have s1 := oC_iter (k := k) (by omega) hke ((k-10)/2) h (by omega)
    set x := (rho k)^[(k-10)/2] j with hx
    have hox : oC x = oC j + (k-10)/2 := s1.2
    rw [tt_C2_id (by omega) hke s1.1 (by omega)]
    have s2 := oC_iter_wrap (k := k) (by omega) hke 8 s1.1 (by omega) (by omega)
    exact ⟨s2.1, by have h4 := s2.2; omega⟩
  · have s1 := oC_iter_wrap (k := k) (by omega) hke ((k-10)/2) h (by omega) (by omega)
    set x := (rho k)^[(k-10)/2] j with hx
    have hox : oC x + 2 = oC j + (k-10)/2 + 2 - (k/2 - 1) := s1.2
    rw [tt_C2_id (by omega) hke s1.1 (by omega)]
    have s2 := oC_iter (k := k) (by omega) hke 8 s1.1 (by omega)
    exact ⟨s2.1, by have h4 := s2.2; omega⟩

theorem loc8 (hk : 20 ≤ k) (hke : k % 2 = 0) {j : ℕ} (h : inC2 k j)
    (h1 : oC j + 2 ≠ k / 2) (h2 : oC j ≠ 3) (h3 : k / 2 < oC j + 6) :
    inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = oC j + 4 - (k / 2 - 1) := by
  have hb : oC j + 2 ≤ k / 2 := by unfold inC2 at h; unfold oC; omega
  rw [tauW_fOne (by omega) hke, tt_C2_id (by omega) hke h h1]
  have s1 := oC_iter_wrap (k := k) (by omega) hke ((k-10)/2) h (by omega) (by omega)
  set x := (rho k)^[(k-10)/2] j with hx
  have hox : oC x + 2 = oC j + (k-10)/2 + 2 - (k/2 - 1) := s1.2
  rw [tt_C2_id (by omega) hke s1.1 (by omega)]
  have s2 := oC_iter_wrap (k := k) (by omega) hke 8 s1.1 (by omega) (by omega)
  exact ⟨s2.1, by have h4 := s2.2; omega⟩

theorem proof :
  ∀ k : ℕ, 20 ≤ k → k % 2 = 0 → ∀ j : ℕ,
    (inC1 k j → eC j = k / 2 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = 3) ∧
    (inC1 k j → eC j = 5 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = 7) ∧
    (inC1 k j → eC j ≠ k / 2 → eC j ≠ 5 → eC j + 2 ≤ k / 2 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = eC j + 2) ∧
    (inC1 k j → eC j ≠ k / 2 → eC j ≠ 5 → k / 2 < eC j + 2 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = eC j + 2 - (k / 2 + 1)) ∧
    (inC2 k j → oC j + 2 = k / 2 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = 1) ∧
    (inC2 k j → oC j = 3 →
        inC1 k (tauW k (fOne k) j) ∧ eC (tauW k (fOne k) j) = 7) ∧
    (inC2 k j → oC j + 2 ≠ k / 2 → oC j ≠ 3 → oC j + 6 ≤ k / 2 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = oC j + 4) ∧
    (inC2 k j → oC j + 2 ≠ k / 2 → oC j ≠ 3 → k / 2 < oC j + 6 →
        inC2 k (tauW k (fOne k) j) ∧ oC (tauW k (fOne k) j) = oC j + 4 - (k / 2 - 1)) := by
  intro k hk hke j
  exact ⟨fun h he => loc1 hk hke h he,
         fun h he => loc2 hk hke h he,
         fun h a b c => loc3 hk hke h a b c,
         fun h a b c => loc4 hk hke h a b c,
         fun h he => loc5 hk hke h he,
         fun h he => loc6 hk hke h he,
         fun h a b c => loc7 hk hke h a b c,
         fun h a b c => loc8 hk hke h a b c⟩

end Submissions.CurrieMolTauLocalRuleEvenK.LocalRule
