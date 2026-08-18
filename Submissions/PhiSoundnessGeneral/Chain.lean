import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.VecNotation

namespace Submissions.PhiSoundnessGeneral.Chain


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


/-- **Soundness of Kontsevich's certificate in every cell dimension.**

The proof is the module algebra of the `p = 2` case verbatim, with `2` replaced by `p` —
which is possible because the argument never mentions the dimension.  Three steps:

1. Each admissible cell's defect `cellPhi Φ z - taut z` lies in `L`, so the integer combination
   `∑ᵢ cᵢ • (cellPhi Φ (zᵢ) - taut (zᵢ))` lies in `L`, `L` being a subgroup.
2. That combination is `(∑ᵢ cᵢ • cellPhi Φ (zᵢ)) - (∑ᵢ cᵢ • taut (zᵢ))`.
3. The first summand is `0` because the chain is balanced (apply the hypothesis at `Ψ := Φ`).
   So `-(∑ᵢ cᵢ • taut (zᵢ)) ∈ L`, hence `∑ᵢ cᵢ • taut (zᵢ) ∈ L`. -/
theorem proof : ∀ (N m p : ℕ) (M : Type) [_inst : AddCommGroup M]
    (taut : Cell N m p → M) (adm : Cell N m p → Prop)
    (L : Submodule ℤ M) (Φ : PhiFam N m p M),
      (∀ z : Cell N m p, adm z → cellPhi Φ z - taut z ∈ L) →
      ∀ (ι : Type) (s : Finset ι) (c : ι → ℤ) (z : ι → Cell N m p),
        (∀ i ∈ s, adm (z i)) →
        (∀ Ψ : PhiFam N m p M, ∑ i ∈ s, c i • cellPhi Ψ (z i) = 0) →
        ∑ i ∈ s, c i • taut (z i) ∈ L := by
  intro N m p M _inst taut adm L Φ hdef ι s c z hadm hbal
  -- 1. the combination of defects lies in `L`
  have hmem : ∑ i ∈ s, c i • (cellPhi Φ (z i) - taut (z i)) ∈ L :=
    Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hdef (z i) (hadm i hi))
  -- 2. it is the `Φ`-side minus the tautological class
  have hsplit : ∑ i ∈ s, c i • (cellPhi Φ (z i) - taut (z i))
      = (∑ i ∈ s, c i • cellPhi Φ (z i)) - ∑ i ∈ s, c i • taut (z i) := by
    simp [smul_sub, Finset.sum_sub_distrib]
  -- 3. the `Φ`-side vanishes: the chain is balanced
  rw [hsplit, hbal Φ, zero_sub] at hmem
  exact (Submodule.neg_mem_iff L).mp hmem

end Submissions.PhiSoundnessGeneral.Chain
