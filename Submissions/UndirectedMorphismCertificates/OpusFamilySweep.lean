import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
Every clause is a finite computation over `{1,…,k}` for ten explicit `k`, discharged by
`decide`. `maxRecDepth` and `maxHeartbeats` are raised because the elaborator builds one
`Decidable` term covering all ten rows; neither option touches the kernel, which rechecks the
whole term, and the axiom audit is `{propext, Classical.choice, Quot.sound}`.
-/

namespace Submissions.UndirectedMorphismCertificates.OpusFamilySweep
/-- Currie–Mol's `σ(m)` acting on the letter `j` of `Σ_k = {1,…,k}`: fixes `1,…,m-1`,
sends `j ↦ j+1` for `m ≤ j ≤ k-1`, and sends `k ↦ m`. Spelled exactly as
`Statements.TauNormalForm.sig`. -/
def sig (k m j : ℕ) : ℕ := if j < m then j else if j = k then m else j + 1

/-- `σ(t₁ ⋯ tₙ)` applied to `j`: `σ` is a morphism into `S_k` and the product is ordinary
function composition, so the LAST letter acts first. -/
def act (k : ℕ) (w : List ℕ) (j : ℕ) : ℕ := w.foldr (sig k) j

/-- `g(1) = 31`, `g(2) = 12`: Currie–Mol's fixed binary-to-ternary morphism for `k ∉ {5,6,8}`. -/
def gblock : ℕ → List ℕ
  | 1 => [3, 1]
  | _ => [1, 2]

/-- `g` extended to a morphism on binary words. -/
def gexp (u : List ℕ) : List ℕ := u.flatMap gblock

/-- `τ(u) = σ(g(u))`, applied to the letter `j`. -/
def tau (k : ℕ) (u : List ℕ) (j : ℕ) : ℕ := act k (gexp u) j

/-- The letters `Σ_k = {1,…,k}`. -/
def pts (k : ℕ) : List ℕ := (List.range k).map (· + 1)

/-- One row of the certificate, spelled out: for alphabet size `k`, blocks `a = f_k(1)`,
`b = f_k(2)` and a conjugator `p` given as a `0`-indexed lookup table of length `k+1`,
`φ`, `τ(a)` and `τ(b)` all permute `{1,…,k}` and `φ ∘ τ(a) = τ(1) ∘ φ`, `φ ∘ τ(b) = τ(2) ∘ φ`
on those letters — i.e. `φ · τ(f_k(x)) · φ⁻¹ = τ(x)` for `x ∈ {1,2}`. -/
abbrev ok (k : ℕ) (a b p : List ℕ) : Prop :=
  a.length = b.length ∧ a.head? = some 1 ∧ a.getLast? ≠ b.getLast? ∧ p.length = k + 1 ∧
  ((pts k).map (fun j => p.getD j 0)).Perm (pts k) ∧
  ((pts k).map (tau k a)).Perm (pts k) ∧
  ((pts k).map (tau k b)).Perm (pts k) ∧
  ((pts k).map (tau k a)).map (fun j => p.getD j 0)
      = ((pts k).map (fun j => p.getD j 0)).map (tau k [1]) ∧
  ((pts k).map (tau k b)).map (fun j => p.getD j 0)
      = ((pts k).map (fun j => p.getD j 0)).map (tau k [2])

def data : List (ℕ × List ℕ × List ℕ × List ℕ) :=
  [
   (22, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1],
    [0, 1, 2, 16, 4, 9, 6, 3, 8, 18, 10, 11, 12, 5, 13, 20, 15, 14, 17, 7, 19, 22, 21]),
   (23, [1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1], [1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2],
    [0, 11, 21, 8, 20, 9, 19, 6, 7, 18, 16, 4, 5, 17, 14, 2, 1, 15, 3, 12, 10, 13, 22, 23]),
   (24, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1],
    [0, 11, 1, 8, 13, 14, 2, 20, 15, 3, 4, 10, 17, 16, 5, 22, 19, 6, 7, 12, 21, 18, 9, 24, 23]),
   (28, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 13, 1, 22, 15, 16, 2, 10, 17, 3, 4, 24, 19, 18, 5, 12, 21, 6, 7, 26, 23, 20, 9, 14, 25, 8, 11, 28, 27]),
   (32, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 15, 1, 10, 17, 18, 2, 26, 19, 3, 4, 12, 21, 20, 5, 28, 23, 6, 7, 14, 25, 22, 9, 30, 27, 8, 11, 16, 29, 24, 13, 32, 31]),
   (36, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 17, 1, 28, 19, 20, 2, 12, 21, 3, 4, 30, 23, 22, 5, 14, 25, 6, 7, 32, 27, 24, 9, 16, 29, 8, 11, 34, 31, 26, 13, 18, 33, 10, 15, 36, 35]),
   (40, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 19, 1, 12, 21, 22, 2, 32, 23, 3, 4, 14, 25, 24, 5, 34, 27, 6, 7, 16, 29, 26, 9, 36, 31, 8, 11, 18, 33, 28, 13, 38, 35, 10, 15, 20, 37, 30, 17, 40, 39]),
   (44, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 21, 1, 34, 23, 24, 2, 14, 25, 3, 4, 36, 27, 26, 5, 16, 29, 6, 7, 38, 31, 28, 9, 18, 33, 8, 11, 40, 35, 30, 13, 20, 37, 10, 15, 42, 39, 32, 17, 22, 41, 12, 19, 44, 43]),
   (48, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 23, 1, 14, 25, 26, 2, 38, 27, 3, 4, 16, 29, 28, 5, 40, 31, 6, 7, 18, 33, 30, 9, 42, 35, 8, 11, 20, 37, 32, 13, 44, 39, 10, 15, 22, 41, 34, 17, 46, 43, 12, 19, 24, 45, 36, 21, 48, 47]),
   (52, [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [0, 25, 1, 40, 27, 28, 2, 16, 29, 3, 4, 42, 31, 30, 5, 18, 33, 6, 7, 44, 35, 32, 9, 20, 37, 8, 11, 46, 39, 34, 13, 22, 41, 10, 15, 48, 43, 36, 17, 24, 45, 12, 19, 50, 47, 38, 21, 26, 49, 14, 23, 52, 51])
  ]

/-- The canonical proposition: every row of `data` carries a uniform binary morphism `f_k` and
a permutation `φ` of `{1,…,k}` with Moulin-Ollagnier's algebraic property
`φ · τ(f_k(x)) · φ⁻¹ = τ(x)` for `x ∈ {1,2}`, together with the two block side-conditions
Currie–Mol's Theorem 5 uses. -/
abbrev statement : Prop := ∀ d ∈ data, ok d.1 d.2.1 d.2.2.1 d.2.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The algebraic property for all ten rows. -/
theorem proof : statement := by decide

end Submissions.UndirectedMorphismCertificates.OpusFamilySweep
