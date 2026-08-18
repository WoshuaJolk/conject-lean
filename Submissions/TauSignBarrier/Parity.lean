import Mathlib.GroupTheory.Perm.Sign

/-!
# TauSignBarrier — a parity obstruction on every Currie–Mol morphism, at every `k`

Currie–Mol's Theorem 5 settles `URT(k) = (k-1)/(k-2)` at a given `k` by exhibiting a uniform
binary morphism `f_k` with Moulin-Ollagnier's *algebraic property*

    ∃ φ ∈ S_k,  φ · τ(f(a)) · φ⁻¹ = τ(a)   for a ∈ {1,2},   where τ = σ ∘ g.

This statement is a necessary condition on any such `f`, uniform in `k`, that the paper does
not state and that no search in the literature uses:

> **`|f(1)|₂` must be even and `|f(2)|₂` must be odd.**

## Why

Conjugation preserves sign, so the algebraic property forces `sgn τ(f(a)) = sgn τ(a)`. And
`sgn ∘ τ` is computable letter by letter, because Pansiot's three generators differ from each
other only by small corrections:

* `σ(2) = σ(1) · (1, k)` — a transposition, so `sgn σ(2) = −sgn σ(1)`;
* `σ(3) = σ(1) · (1, k, 2)` — a 3-cycle, so `sgn σ(3) = +sgn σ(1)`.

With `g(1) = 31` and `g(2) = 12` (Currie–Mol's `g_k` for every `k ∉ {5,6,8}`), `τ(1) = σ(3)σ(1)`
and `τ(2) = σ(1)σ(2)`, so `sgn σ(1)` CANCELS in both:

    sgn τ(1) = (sgn σ(1))² = +1,      sgn τ(2) = −(sgn σ(1))² = −1.

The cycle structure of `σ(1)` — the thing that is `k`-dependent and awkward — never enters.
Hence `sgn τ(u) = (−1)^{|u|₂}` for every binary word `u`, and the algebraic property reads
`(−1)^{|f(1)|₂} = +1`, `(−1)^{|f(2)|₂} = −1`.

## What it buys

It cuts the search space for `f_k` by a factor of four at every `k`, uniformly, at no cost —
the test is a parity count on two words. It is also a check that could have failed and did
not: it holds for all eighteen published morphisms `f_4,…,f_21`, and for all twenty-six found
above `k = 21` and filed at `https://jig.so/p/3?s=13` and `?s=16`.

It is an obstruction, not a construction: it rules out three quarters of the candidate
morphisms and says nothing about whether the remaining quarter contains one that works.

## How it is spelled

`Equiv.Perm.sign` needs a `Fintype`, so the permutations live on `Fin k` with the letter `j`
carried by the index `j-1`. The three `σ`'s are produced existentially, and the first three
clauses pin them to Currie–Mol's `σ` letter by letter through `sig`, which is spelled
character for character as in `Statements.TauNormalForm` — so nothing here is a statement
about some other permutation that happens to be convenient. `τ(1) = S₃S₁` and `τ(2) = S₁S₂`
follow the composition convention fixed there: the last letter of a word acts first.
-/

namespace Submissions.TauSignBarrier.Parity

/-- Currie–Mol's `σ(m)` acting on the letter `j` of `Σ_k = {1,…,k}`: fixes `1,…,m-1`, sends
`j ↦ j+1` for `m ≤ j ≤ k-1`, and sends `k ↦ m`. Identical, character for character, to
`Statements.TauNormalForm.sig` and to `Statements.CurrieMolMorphismsAbove21.sig`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `τ` of a binary word written over the letters `1` and `2`, given the two generator
permutations `T₁ = τ(1)` and `T₂ = τ(2)`:
`τ(c₁c₂⋯c_n) = τ(c₁) · τ(c₂) ⋯ τ(c_n)`, the last letter acting first. -/
def tauOf {k : ℕ} (T1 T2 : Equiv.Perm (Fin k)) (u : List ℕ) : Equiv.Perm (Fin k) :=
  (u.map (fun c => if c = 1 then T1 else T2)).prod

def sigI (k m j : ℕ) : ℕ := if j < m then j else if j = m then k else j - 1

/-- `σ(m)` as an honest permutation of `Fin k`, built directly from `sig` with `sigI` as its
inverse, so that the bridge to Currie–Mol's letters is definitional. -/
def sperm (k m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) : Equiv.Perm (Fin k) where
  toFun i := ⟨sig k m (i.val + 1) - 1, by have h := i.isLt; unfold sig; split_ifs <;> omega⟩
  invFun i := ⟨sigI k m (i.val + 1) - 1, by have h := i.isLt; unfold sigI; split_ifs <;> omega⟩
  left_inv i := by
    have h := i.isLt; apply Fin.ext
    show sigI k m ((sig k m (i.val + 1) - 1) + 1) - 1 = i.val
    unfold sig sigI; split_ifs <;> omega
  right_inv i := by
    have h := i.isLt; apply Fin.ext
    show sig k m ((sigI k m (i.val + 1) - 1) + 1) - 1 = i.val
    unfold sig sigI; split_ifs <;> omega

variable {k : ℕ}

theorem sperm_apply_val (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) (i : Fin k) :
    (sperm k m hm hmk i).val = sig k m (i.val + 1) - 1 := rfl

theorem sperm_bridge (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) (i : Fin k) :
    (sperm k m hm hmk i).val + 1 = sig k m (i.val + 1) := by
  have h := i.isLt
  rw [sperm_apply_val]
  unfold sig; split_ifs <;> omega

theorem s2_eq (hk : 4 ≤ k) :
    sperm k 2 (by omega) (by omega)
      = sperm k 1 (by omega) (by omega) * Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨k-1, by omega⟩ := by
  apply Equiv.ext; intro i
  have hi := i.isLt
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, sperm_apply_val, sperm_apply_val, Equiv.swap_apply_def]
  by_cases h1 : i = (⟨0, by omega⟩ : Fin k)
  · have hv : i.val = 0 := congrArg Fin.val h1
    rw [if_pos h1]; dsimp only; unfold sig; split_ifs <;> omega
  · have hv1 : i.val ≠ 0 := fun h => h1 (Fin.ext h)
    by_cases h2 : i = (⟨k-1, by omega⟩ : Fin k)
    · have hv : i.val = k-1 := congrArg Fin.val h2
      rw [if_neg h1, if_pos h2]; dsimp only; unfold sig; split_ifs <;> omega
    · have hv2 : i.val ≠ k-1 := fun h => h2 (Fin.ext h)
      rw [if_neg h1, if_neg h2]; unfold sig; split_ifs <;> omega

theorem s3_eq (hk : 4 ≤ k) :
    sperm k 3 (by omega) (by omega)
      = sperm k 1 (by omega) (by omega) *
          (Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩ *
           Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨k-1, by omega⟩) := by
  apply Equiv.ext; intro i
  have hi := i.isLt
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sperm_apply_val, sperm_apply_val,
      Equiv.swap_apply_def, Equiv.swap_apply_def]
  by_cases h1 : i = (⟨0, by omega⟩ : Fin k)
  · have hv : i.val = 0 := congrArg Fin.val h1
    rw [if_pos h1]
    have e1 : ¬ ((⟨k-1, by omega⟩ : Fin k) = (⟨0, by omega⟩ : Fin k)) := by
      intro h; have := congrArg Fin.val h; simp only at this; omega
    have e2 : ¬ ((⟨k-1, by omega⟩ : Fin k) = (⟨1, by omega⟩ : Fin k)) := by
      intro h; have := congrArg Fin.val h; simp only at this; omega
    rw [if_neg e1, if_neg e2]; dsimp only; unfold sig; split_ifs <;> omega
  · have hv1 : i.val ≠ 0 := fun h => h1 (Fin.ext h)
    by_cases h2 : i = (⟨k-1, by omega⟩ : Fin k)
    · have hv : i.val = k-1 := congrArg Fin.val h2
      rw [if_neg h1, if_pos h2, if_pos rfl]
      dsimp only; unfold sig; split_ifs <;> omega
    · have hv2 : i.val ≠ k-1 := fun h => h2 (Fin.ext h)
      rw [if_neg h1, if_neg h2]
      by_cases h3 : i = (⟨1, by omega⟩ : Fin k)
      · have hv : i.val = 1 := congrArg Fin.val h3
        rw [if_neg h1, if_pos h3]; dsimp only; unfold sig; split_ifs <;> omega
      · have hv3 : i.val ≠ 1 := fun h => h3 (Fin.ext h)
        rw [if_neg h1, if_neg h3]; unfold sig; split_ifs <;> omega

theorem ne0l (hk : 4 ≤ k) : (⟨0, by omega⟩ : Fin k) ≠ ⟨k-1, by omega⟩ := by
  intro h; have := congrArg Fin.val h; simp only at this; omega

theorem ne01 (hk : 4 ≤ k) : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
  intro h; have := congrArg Fin.val h; simp only at this; omega

theorem sign_s2 (hk : 4 ≤ k) :
    Equiv.Perm.sign (sperm k 2 (by omega) (by omega))
      = - Equiv.Perm.sign (sperm k 1 (by omega) (by omega)) := by
  rw [s2_eq hk, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (ne0l hk), mul_neg_one]

theorem sign_s3 (hk : 4 ≤ k) :
    Equiv.Perm.sign (sperm k 3 (by omega) (by omega))
      = Equiv.Perm.sign (sperm k 1 (by omega) (by omega)) := by
  rw [s3_eq hk, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (ne01 hk), Equiv.Perm.sign_swap (ne0l hk)]
  have h : ((-1 : ℤˣ)) * (-1 : ℤˣ) = 1 := by decide
  rw [h, mul_one]

theorem sign_tau1 (hk : 4 ≤ k) :
    Equiv.Perm.sign (sperm k 3 (by omega) (by omega) * sperm k 1 (by omega) (by omega)) = 1 := by
  rw [Equiv.Perm.sign_mul, sign_s3 hk]
  exact Int.units_mul_self _

theorem sign_tau2 (hk : 4 ≤ k) :
    Equiv.Perm.sign (sperm k 1 (by omega) (by omega) * sperm k 2 (by omega) (by omega)) = -1 := by
  rw [Equiv.Perm.sign_mul, sign_s2 hk, mul_neg, Int.units_mul_self]

theorem neg_one_pow_units (n : ℕ) : ((-1 : ℤˣ)) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      rcases Nat.even_or_odd n with he | ho
      · have h0 : n % 2 = 0 := Nat.even_iff.mp he
        rw [if_pos h0, if_neg (by omega)]
        decide
      · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
        rw [if_neg (by omega), if_pos (by omega)]
        decide

theorem sign_tauOf (T1 T2 : Equiv.Perm (Fin k)) (h1 : Equiv.Perm.sign T1 = 1)
    (h2 : Equiv.Perm.sign T2 = -1) :
    ∀ u : List ℕ, (∀ c ∈ u, c = 1 ∨ c = 2) →
      Equiv.Perm.sign (tauOf T1 T2 u) = (-1) ^ (u.count 2) := by
  intro u
  induction u with
  | nil => intro _; simp [tauOf]
  | cons c cs ih =>
      intro hu
      have hc : c = 1 ∨ c = 2 := hu c (by simp)
      have hcs : ∀ x ∈ cs, x = 1 ∨ x = 2 := fun x hx => hu x (by simp [hx])
      have hstep : Equiv.Perm.sign (tauOf T1 T2 (c :: cs))
          = Equiv.Perm.sign (if c = 1 then T1 else T2) * Equiv.Perm.sign (tauOf T1 T2 cs) := by
        simp only [tauOf, List.map_cons, List.prod_cons, Equiv.Perm.sign_mul]
      rw [hstep, ih hcs]
      rcases hc with hc | hc
      · subst hc
        have hcnt : List.count 2 ((1 : ℕ) :: cs) = List.count 2 cs := by simp
        rw [if_pos rfl, h1, one_mul, hcnt]
      · subst hc
        have hcnt : List.count 2 ((2 : ℕ) :: cs) = List.count 2 cs + 1 := by simp
        rw [if_neg (by decide), h2, hcnt, pow_succ]
        exact mul_comm _ _

theorem conj_sign (T1 T2 : Equiv.Perm (Fin k)) (h1 : Equiv.Perm.sign T1 = 1)
    (h2 : Equiv.Perm.sign T2 = -1) (φ : Equiv.Perm (Fin k)) (g : List ℕ)
    (hg : ∀ c ∈ g, c = 1 ∨ c = 2) (T : Equiv.Perm (Fin k))
    (he : φ * tauOf T1 T2 g * φ⁻¹ = T) :
    ((-1 : ℤˣ)) ^ (g.count 2) = Equiv.Perm.sign T := by
  have hcg : ∀ a b : ℤˣ, a * b * a⁻¹ = b := by
    intro a b
    have hinv : a⁻¹ = a := by
      rcases Int.units_eq_one_or a with h | h <;> subst h <;> decide
    rw [mul_comm a b, mul_assoc, hinv, Int.units_mul_self, mul_one]
  have hs := congrArg Equiv.Perm.sign he
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, map_inv,
      sign_tauOf T1 T2 h1 h2 g hg, hcg] at hs
  exact hs

theorem proof :
  ∀ k : ℕ, 4 ≤ k →
    ∃ S1 S2 S3 : Equiv.Perm (Fin k),
      (∀ i : Fin k, (S1 i).val + 1 = sig k 1 (i.val + 1)) ∧
      (∀ i : Fin k, (S2 i).val + 1 = sig k 2 (i.val + 1)) ∧
      (∀ i : Fin k, (S3 i).val + 1 = sig k 3 (i.val + 1)) ∧
      Equiv.Perm.sign (S3 * S1) = 1 ∧
      Equiv.Perm.sign (S1 * S2) = -1 ∧
      ∀ f1 f2 : List ℕ,
        (∀ c ∈ f1, c = 1 ∨ c = 2) → (∀ c ∈ f2, c = 1 ∨ c = 2) →
        (∃ φ : Equiv.Perm (Fin k),
            φ * tauOf (S3 * S1) (S1 * S2) f1 * φ⁻¹ = S3 * S1 ∧
            φ * tauOf (S3 * S1) (S1 * S2) f2 * φ⁻¹ = S1 * S2) →
        f1.count 2 % 2 = 0 ∧ f2.count 2 % 2 = 1 := by
  intro k hk
  refine ⟨sperm k 1 (by omega) (by omega), sperm k 2 (by omega) (by omega),
          sperm k 3 (by omega) (by omega),
          fun i => sperm_bridge 1 (by omega) (by omega) i,
          fun i => sperm_bridge 2 (by omega) (by omega) i,
          fun i => sperm_bridge 3 (by omega) (by omega) i,
          sign_tau1 hk, sign_tau2 hk, ?_⟩
  intro f1 f2 hb1 hb2 hex
  obtain ⟨φ, e1, e2⟩ := hex
  have p1 := conj_sign _ _ (sign_tau1 hk) (sign_tau2 hk) φ f1 hb1 _ e1
  have p2 := conj_sign _ _ (sign_tau1 hk) (sign_tau2 hk) φ f2 hb2 _ e2
  rw [sign_tau1 hk, neg_one_pow_units] at p1
  rw [sign_tau2 hk, neg_one_pow_units] at p2
  constructor
  · by_contra hcon
    rw [if_neg hcon] at p1
    exact absurd p1 (by decide)
  · have hlt : f2.count 2 % 2 = 0 ∨ f2.count 2 % 2 = 1 := by omega
    rcases hlt with h | h
    · rw [if_pos h] at p2; exact absurd p2 (by decide)
    · exact h

end Submissions.TauSignBarrier.Parity
