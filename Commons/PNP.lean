import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
`Commons.PNP` is the shared vocabulary for the P-vs-NP problem: a decision problem is a
set of bitstrings (`Lang`), `P` is decidability by a `Turing.TM2` machine running in
time bounded by a polynomial in the input length (Mathlib's own
`Turing.TM2ComputableInPolyTime`), and `NP` is the certificate/verifier definition: a
polynomial `p` and a poly-time verifier on (instance, certificate) pairs that accepts
`w` iff some certificate of length at most `p (|w|)` makes it accept.
-/

namespace Commons.PNP

open scoped Classical
open Turing Computability

/-- A decision problem: a set of finite bitstrings. -/
abbrev Lang := Set (List Bool)

/-- `L` is decided by a multi-tape Turing machine (`Turing.TM2`) running in time bounded
by a polynomial in the length of the input, the standard definition of the complexity
class `P`. -/
noncomputable def InP (L : Lang) : Prop :=
  Nonempty (TM2ComputableInPolyTime (encodingList Bool).encode encodeBool
    (fun w => decide (w ∈ L)))

/-- A `Bool`-alphabet encoding of an (instance, certificate) pair: the length of the
instance `w` in unary (a run of `w.length` copies of `true`), a `false` marker, then `w`
and the certificate `c` concatenated. Reading off the leading run of `true`s up to the
first `false` recovers `w.length`, and hence `w` and `c` separately, so this is
injective — no information is lost by flattening the pair onto one `Bool` tape. -/
def pairEncode (p : List Bool × List Bool) : List Bool :=
  List.replicate p.1.length true ++ false :: (p.1 ++ p.2)

/-- `L` is verified in polynomial time: there is a polynomial `p` bounding certificate
length and a poly-time decidable verifier `V` on (instance, certificate) pairs such that
`w ∈ L` iff some certificate `c` with `c.length ≤ p.eval w.length` makes `V` accept. This
is the certificate/verifier definition of `NP` (Sipser, *Introduction to the Theory of
Computation*, 3rd ed., §7.3, Definition 7.19). -/
noncomputable def InNP (L : Lang) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    Nonempty (TM2ComputableInPolyTime pairEncode encodeBool V) ∧
    ∀ w, w ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

/-- The complexity class `P`, as a set of languages. -/
def P : Set Lang := {L | InP L}

/-- The complexity class `NP`, as a set of languages. -/
def NP : Set Lang := {L | InNP L}

/-! ### A witness: the empty language is in both `P` and `NP`

This is the smoke test for the definitions above: it exhibits a genuine `TM2` machine
(not an appeal to `Nonempty` in the abstract) for both `InP` and `InNP`, which is what
rules out the definitions being vacuous (unsatisfiable, in which case *every* statement
of the form `InP L` or `InNP L` would be unprovable and `P = NP` could be "refuted" by a
bug in the encoding rather than by mathematics). -/

open Turing.TM2.Stmt in
/-- A one-stack machine that discards whatever is on its stack and writes `false`. -/
def falseComputer : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ o => o.isSome)
      (branch id (goto (fun _ => ())) (push () (fun _ => false) halt))

/-- Running `falseComputer` for `l.length + 1` steps from a stack holding `l` always
halts with the single stack holding exactly `[false]`. -/
theorem falseComputer_reaches (l : List Bool) (v : Bool) :
    (flip Option.bind falseComputer.step)^[l.length + 1]
        (some (⟨some (), v, fun _ => l⟩ : falseComputer.Cfg))
      = some (⟨none, false, fun _ => [false]⟩ : falseComputer.Cfg) := by
  induction l generalizing v with
  | nil => rfl
  | cons x xs ih =>
    rw [Function.iterate_succ_apply]
    exact ih true

/-- The identity equivalence between `falseComputer`'s (constant) stack alphabet and `Bool`,
spelled out with `id` rather than `Equiv.refl`/`Equiv.cast` so its `.invFun` is literally `id`
and needs no further unfolding downstream. -/
def falseComputerAlphabet {k : Unit} : falseComputer.Γ k ≃ Bool :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- The empty language is decidable in polynomial time: `falseComputer`, run for
`n + 1` steps on an input of length `n`, always halts with output `false`. -/
theorem emptyInP : InP (∅ : Lang) := by
  refine ⟨⟨⟨falseComputer, falseComputerAlphabet, falseComputerAlphabet⟩, Polynomial.X + 1, ?_⟩⟩
  intro a
  have h := falseComputer_reaches a false
  refine ⟨⟨a.length + 1, ?_⟩, by simp [encodingList]⟩
  dsimp only [falseComputer, falseComputerAlphabet]
  simp only [id_eq, encodingList, List.map_id, Set.mem_empty_iff_false, decide_false, encodeBool]
  exact h

/-- The empty language is also verifiable in polynomial time: the verifier that ignores
both the instance and the certificate and always rejects is (vacuously) correct for
`∅`, and it is computed by the same `falseComputer` machine, this time reading the
`pairEncode`d tape. -/
theorem emptyInNP : InNP (∅ : Lang) := by
  refine ⟨0, fun _ => false,
    ⟨⟨⟨falseComputer, falseComputerAlphabet, falseComputerAlphabet⟩, Polynomial.X + 1, ?_⟩⟩, ?_⟩
  · intro a
    have h := falseComputer_reaches (pairEncode a) false
    refine ⟨⟨(pairEncode a).length + 1, ?_⟩, by simp⟩
    dsimp only [falseComputer, falseComputerAlphabet]
    simp only [List.map_id, encodeBool]
    exact h
  · intro w
    simp

end Commons.PNP
