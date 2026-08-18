import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

/-!
# PansiotImportEvenK — the Dejean-import route is dead at even `k` too

`Statements.PansiotCycleDistanceRigidity` kills the route that would settle Currie–Mol's
Conjecture 1 by transporting the large-alphabet Dejean theory (Pansiot's pair `(σ(1), σ(2))`,
Carpi 2007, Currie–Rampersad `n ≥ 27`) to the undirected setting through Currie–Mol's `g`.
Its own scope says, in as many words: *"Says nothing about even `k`, where `ρ` is not even a
`k`-cycle."* This statement is that missing half.

At even `k` the kill is cruder and stronger than the cyclic-distance argument, and needs no
distance at all. `τ(1) = σ(3) ∘ σ(1) = ρ` is the step-2 map. When `k` is even, `ρ` splits
`{1,…,k}` into the orbit of `1` — which is `1` followed by the even letters — and the odd
letters `3, 5, …, k-1`, which it permutes among themselves. So `ρ` has at least two orbits.
Pansiot's `σ(1)` is the `k`-cycle `j ↦ j+1`, which has exactly one. The number of orbits is a
conjugacy invariant, so no `φ ∈ S_k` conjugates `τ(1)` to `σ(1)`, and therefore none
simultaneously conjugates `(τ(1), τ(2))` to `(σ(1), σ(2))`. The reduction the route needs does
not exist at any even `k ≥ 4`.

Combined with `PansiotCycleDistanceRigidity` (odd `k ≥ 5`) this leaves no `k ≥ 4` at which the
import through `g` can be made to work.

## How the two orbit facts are spelled

Rather than developing orbit counting, the statement records the two facts that give it:

* `(ρ)^[n] 1 ≠ 3` for every `n` — the orbit of `1` under `ρ` never reaches `3`, so `3` lies in
  a different orbit and `ρ` has at least two. (The proof is that `{1} ∪ {even letters ≤ k}` is
  `ρ`-invariant when `k` is even, and `3` is not in it. Evenness of `k` is what makes `k-1`
  odd, so the exceptional letter `k-1 ↦ 3` is never reached from `1`; at odd `k` the same set
  is not invariant and indeed `ρ` is then a single `k`-cycle.)
* `(σ(1))^[n] 1 = n+1` for every `n < k` — the orbit of `1` under `σ(1)` is all of `{1,…,k}`,
  so `σ(1)` has exactly one orbit.

The first clause, `σ(3)(σ(1)(j)) = ρ(j)`, is the bridge that makes these facts about
Currie–Mol's `τ(1)` rather than about a free-standing permutation; `sig` and `rho` are spelled
character for character as in `Statements.TauNormalForm`, which carries the same identity with
a green proof.

## Scope, honestly

This is a statement about permutations. It does not touch the conjecture: `URT(k)` is not
mentioned, no construction is ruled out except through the named reduction, and the per-`k`
morphism search — which is the route that actually produces words — is untouched.
-/

namespace Submissions.PansiotImportEvenK.Orbits

/-- Currie–Mol's `σ(m)` acting on the letter `j` of `Σ_k = {1,…,k}`: fixes `1,…,m-1`, sends
`j ↦ j+1` for `m ≤ j ≤ k-1`, and sends `k ↦ m`. Identical, character for character, to
`Statements.TauNormalForm.sig`. `σ(1)` is Pansiot's `k`-cycle. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `ρ`, the step-2 map: `1 ↦ 2`, `j ↦ j+2` for `2 ≤ j ≤ k-2`, `k-1 ↦ 3`, `k ↦ 1`.
Identical to `Statements.TauNormalForm.rho`. -/
def rho (k j : ℕ) : ℕ :=
  if j = 1 then 2 else if j = k - 1 then 3 else if j = k then 1 else j + 2

theorem tau_one (k j : ℕ) (hk : 4 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    sig k 3 (sig k 1 j) = rho k j := by
  unfold sig rho; split_ifs <;> omega

/-- The `ρ`-orbit of `1` stays inside `{1} ∪ {even letters ≤ k}` when `k` is even. -/
theorem orbit_invariant (k : ℕ) (hk : 4 ≤ k) (hke : k % 2 = 0) (n : ℕ) :
    ((rho k)^[n] 1 = 1 ∨ (rho k)^[n] 1 % 2 = 0) ∧ 1 ≤ (rho k)^[n] 1 ∧ (rho k)^[n] 1 ≤ k := by
  induction n with
  | zero =>
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · show (1 : ℕ) ≤ 1
        omega
      · show (1 : ℕ) ≤ k
        omega
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      set x := (rho k)^[n] 1 with hx
      obtain ⟨hpar, hlo, hhi⟩ := ih
      unfold rho
      split_ifs with h1 h2 h3 <;> omega

theorem orbit_misses_three (k : ℕ) (hk : 4 ≤ k) (hke : k % 2 = 0) (n : ℕ) :
    (rho k)^[n] 1 ≠ 3 := by
  have := orbit_invariant k hk hke n
  omega

theorem sigma_one_transitive (k : ℕ) (hk : 4 ≤ k) (n : ℕ) (hn : n < k) :
    (sig k 1)^[n] 1 = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : n < k := by omega
      rw [Function.iterate_succ_apply', ih hn']
      unfold sig
      split_ifs <;> omega

theorem proof :
  ∀ k : ℕ, 4 ≤ k → k % 2 = 0 →
    (∀ j : ℕ, 1 ≤ j → j ≤ k → sig k 3 (sig k 1 j) = rho k j) ∧
    (∀ n : ℕ, (rho k)^[n] 1 ≠ 3) ∧
    (∀ n : ℕ, n < k → (sig k 1)^[n] 1 = n + 1) := by
  intro k hk hke
  exact ⟨fun j hj hjk => tau_one k j hk hj hjk,
         fun n => orbit_misses_three k hk hke n,
         fun n hn => sigma_one_transitive k hk n hn⟩

end Submissions.PansiotImportEvenK.Orbits
