import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Deliberately weakened control for `PhiSoundnessGeneral` — expected RED

This is an honesty gate, not a claim.  It is the canonical proposition with its **conclusion
replaced by its own balancing hypothesis**: instead of concluding that the chain's tautological
class `∑ᵢ cᵢ • taut (zᵢ)` lies in `L`, it concludes only that the chain's `Φ`-side
`∑ᵢ cᵢ • cellPhi Φ (zᵢ)` lies in `L`.  That is immediate — the balancing hypothesis says the
`Φ`-side is `0`, and `0 ∈ L` for any subgroup — and it says nothing whatever about `taut`, so
the defect hypothesis is never used.  Every content-bearing step of the real argument is gone.

The proposition is therefore strictly weaker than `Statements.PhiSoundnessGeneral.statement`,
and the verifier's bridge check `example : Statements.PhiSoundnessGeneral.statement := proof`
must fail.  Submitted with `expect: "red"`, `expect_reason: "restatement"`.  If this greens,
the bridge is not checking what it claims to check and the companion green artifact should not
be trusted either.
-/

namespace Submissions.PhiSoundnessGeneral.Weak


/-- The lattice `Γ₂` of integral slopes, of rank `N`. -/
abbrev G2 (N : ℕ) : Type := Fin N → ℤ

/-- `Γ₂ ⊗ Γ_p` with `Γ_p` of rank `m`: the lattice the vertices `F₀` live in, before the
quotient by the period lattice `Γ₁`. -/
abbrev G2P (N m : ℕ) : Type := Fin N → Fin m → ℤ

/-- The flag datum of a `p`-dimensional cell: the complete slope flag `V₁ ⊂ ⋯ ⊂ V_{p-1}`,
presented by an ordered spanning sequence, `V_r = ⟨w₁, …, w_r⟩`.  At `p = 2` this is a single
direction, Zharkov's `F₁`. -/
abbrev Flag (N p : ℕ) : Type := Fin (p - 1) → G2 N

/-- `⋀^p Γ₂` in coordinates.  `N.choose p` is `6` at `(N,p) = (4,2)` and `70` at `(8,4)`. -/
abbrev Biv (N p : ℕ) : Type := Fin (N.choose p) → ℤ

/-- A family `Φ_{F₀ ; V₁ ⊂ ⋯ ⊂ V_{p-1}} : ⋀^p Γ₂ → M`, given on the coordinate basis. -/
abbrev PhiFam (N m p : ℕ) (M : Type) : Type := G2P N m → Flag N p → Fin (N.choose p) → M

/-- `Φ_{x ; f}` applied to a `p`-vector given in coordinates, using linearity. -/
noncomputable def app {N m p : ℕ} {M : Type} [AddCommGroup M]
    (Φ : PhiFam N m p M) (x : G2P N m) (f : Flag N p) (β : Biv N p) : M :=
  ∑ k : Fin (N.choose p), β k • Φ x f k

/-- A `p`-dimensional cell, presented by the left-hand side of its relation.  `z.1` is the
signed list of `(coefficient, vertex, flag)` terms of the cell's flag sum, and `z.2` is the
volume element of `⋀^p Γ₂` at which `Φ` is evaluated — the primitive generator of `⋀^p` of the
cell's slope lattice. -/
abbrev Cell (N m p : ℕ) : Type := List (ℤ × G2P N m × Flag N p) × Biv N p

/-- The `Φ`-side of a cell's relation: its signed flag sum. -/
noncomputable def cellPhi {N m p : ℕ} {M : Type} [AddCommGroup M]
    (Φ : PhiFam N m p M) (z : Cell N m p) : M :=
  (z.1.map fun t => t.1 • app Φ t.2.1 t.2.2 z.2).sum

/-- The canonical proposition.  This is the type the verifier demands.

Soundness of Kontsevich's certificate in cell dimension `p`: if `Φ` satisfies the cell relations
modulo `L` at every admissible cell, then every balanced finite chain of admissible cells has
its tautological class in `L`.  Balancing is `∀ Ψ, … = 0`: the `Φ`-side of the chain vanishes
identically in `Φ`. -/
abbrev statement : Prop :=
  ∀ (N m p : ℕ) (M : Type) [_inst : AddCommGroup M]
    (taut : Cell N m p → M) (adm : Cell N m p → Prop)
    (L : Submodule ℤ M) (Φ : PhiFam N m p M),
      (∀ z : Cell N m p, adm z → cellPhi Φ z - taut z ∈ L) →
      ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell N m p),
        (∀ i ∈ s, adm (z i)) →
        (∀ Ψ : PhiFam N m p M, ∑ i ∈ s, c i • cellPhi Ψ (z i) = 0) →
        ∑ i ∈ s, c i • taut (z i) ∈ L



/-- The weakened proposition: the conclusion is the balancing hypothesis restated. -/
theorem proof : ∀ (N m p : ℕ) (M : Type) [_inst : AddCommGroup M]
    (taut : Cell N m p → M) (adm : Cell N m p → Prop)
    (L : Submodule ℤ M) (Φ : PhiFam N m p M),
      (∀ z : Cell N m p, adm z → cellPhi Φ z - taut z ∈ L) →
      ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell N m p),
        (∀ i ∈ s, adm (z i)) →
        (∀ Ψ : PhiFam N m p M, ∑ i ∈ s, c i • cellPhi Ψ (z i) = 0) →
        ∑ i ∈ s, c i • cellPhi Φ (z i) ∈ L := by
  intro N m p M _inst taut adm L Φ _hdef ι s c z _hadm hbal
  rw [hbal Φ]
  exact L.zero_mem

end Submissions.PhiSoundnessGeneral.Weak
