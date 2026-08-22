/-
  RoundRobinUnionConnectivity: a union of D ≥ 2 consecutive round-robin one-factors
  of K_{2M+2} is D-connected (deletion form).

  Proof follows the audited "fattening lemma" argument:
  for nonempty W ⊆ ZMod n (n odd) with cyclic gaps g_w, |W + {0..D-1}| = Σ_w min(g_w, D).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Submissions.RoundRobinUnionConnectivity.RoundRobinConn

/-- The vertex set of `K_m` for `m = 2*M + 2`: the odd cyclic group with a point at infinity. -/
abbrev V (M : ℕ) : Type := Option (ZMod (2 * M + 1))

/-- The relation defining the union of the first `D` round-robin one-factors: two finite points
are related when their sum is `2t` for some `t < D`, and `∞` is related to each `t < D`. -/
def rel (M D : ℕ) : V M → V M → Prop
  | none, some b => ∃ t : ℕ, t < D ∧ b = (t : ZMod (2 * M + 1))
  | some a, some b => ∃ t : ℕ, t < D ∧ a + b = 2 * (t : ZMod (2 * M + 1))
  | _, _ => False

/-- The union of the first `D` one-factors of the round-robin one-factorization of `K_m`. -/
def unionGraph (M D : ℕ) : SimpleGraph (V M) := SimpleGraph.fromRel (rel M D)

/-! ### Cyclic-gap machinery over `ZMod n` -/

section Gaps

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Casting is injective below `n`. -/
lemma cast_inj_of_lt {j k : ℕ} (hj : j < n) (hk : k < n)
    (h : (j : ZMod n) = (k : ZMod n)) : j = k := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hj, ZMod.val_cast_of_lt hk] at this

/-- `seg w m` is the "arc" `{w, w+1, …, w+(m-1)}` in `ZMod n`. -/
def seg (w : ZMod n) (m : ℕ) : Finset (ZMod n) :=
  (Finset.range m).image (fun j : ℕ => w + (j : ZMod n))

omit [NeZero n] in
lemma mem_seg {w x : ZMod n} {m : ℕ} :
    x ∈ seg w m ↔ ∃ j : ℕ, j < m ∧ x = w + (j : ZMod n) := by
  simp only [seg, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

omit [NeZero n] in
lemma seg_card {w : ZMod n} {m : ℕ} (hm : m ≤ n) : (seg w m).card = m := by
  rw [seg, Finset.card_image_of_injOn, Finset.card_range]
  intro j hj k hk h
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  exact cast_inj_of_lt (lt_of_lt_of_le hj hm) (lt_of_lt_of_le hk hm)
    (add_left_cancel h)

/-- The cyclic gap of `w` relative to `W`: the least `g ≥ 1` with `w + g ∈ W`
(with a harmless default making it always ≤ n). -/
def gap (W : Finset (ZMod n)) (w : ZMod n) : ℕ :=
  Nat.find (p := fun g => g = n ∨ (0 < g ∧ w + (g : ZMod n) ∈ W)) ⟨n, Or.inl rfl⟩

lemma gap_pos (W : Finset (ZMod n)) (w : ZMod n) : 0 < gap W w := by
  have h := Nat.find_spec (p := fun g => g = n ∨ (0 < g ∧ w + (g : ZMod n) ∈ W)) ⟨n, Or.inl rfl⟩
  rcases h with h | h
  · rw [gap, h]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  · exact h.1

omit [NeZero n] in
lemma gap_le (W : Finset (ZMod n)) (w : ZMod n) : gap W w ≤ n :=
  Nat.find_le (Or.inl rfl)

omit [NeZero n] in
lemma add_gap_mem {W : Finset (ZMod n)} {w : ZMod n} (hw : w ∈ W) :
    w + (gap W w : ZMod n) ∈ W := by
  have h := Nat.find_spec (p := fun g => g = n ∨ (0 < g ∧ w + (g : ZMod n) ∈ W)) ⟨n, Or.inl rfl⟩
  rcases h with h | h
  · rw [gap, h]; simpa [ZMod.natCast_self] using hw
  · exact h.2

omit [NeZero n] in
lemma not_mem_of_lt_gap {W : Finset (ZMod n)} {w : ZMod n} {j : ℕ}
    (hj0 : 0 < j) (hj : j < gap W w) : w + (j : ZMod n) ∉ W := by
  intro hmem
  exact Nat.find_min (p := fun g => g = n ∨ (0 < g ∧ w + (g : ZMod n) ∈ W))
    ⟨n, Or.inl rfl⟩ hj (Or.inr ⟨hj0, hmem⟩)

/-- Every point of `ZMod n` lies on the arc of some element of `W` (when `W` is nonempty). -/
lemma arc_cover {W : Finset (ZMod n)} (hW : W.Nonempty) (x : ZMod n) :
    ∃ w ∈ W, ∃ j : ℕ, j < gap W w ∧ x = w + (j : ZMod n) := by
  obtain ⟨w', hw'⟩ := hW
  have hex : ∃ δ : ℕ, x - (δ : ZMod n) ∈ W := by
    refine ⟨(x - w').val, ?_⟩
    rw [ZMod.natCast_zmod_val]
    simpa using hw'
  set δ := Nat.find hex with hδdef
  have hδW : x - (δ : ZMod n) ∈ W := Nat.find_spec hex
  have hxw : x = x - (δ : ZMod n) + (δ : ZMod n) := by ring
  refine ⟨x - (δ : ZMod n), hδW, δ, ?_, hxw⟩
  rcases Nat.lt_or_ge δ (gap W (x - (δ : ZMod n))) with hlt | hge
  · exact hlt
  · exfalso
    have hg0 : 0 < gap W (x - (δ : ZMod n)) := gap_pos W _
    have hmem : (x - (δ : ZMod n)) + (gap W (x - (δ : ZMod n)) : ZMod n) ∈ W :=
      add_gap_mem hδW
    have hsub : x - ((δ - gap W (x - (δ : ZMod n)) : ℕ) : ZMod n) ∈ W := by
      rw [Nat.cast_sub hge]
      have heq : x - ((δ : ZMod n) - (gap W (x - (δ : ZMod n)) : ZMod n)) =
          (x - (δ : ZMod n)) + (gap W (x - (δ : ZMod n)) : ZMod n) := by ring
      rw [heq]
      exact hmem
    exact Nat.find_min hex (by omega) hsub

omit [NeZero n] in
/-- Two arcs meeting in a point coincide (one-sided version). -/
lemma arc_eq_aux {W : Finset (ZMod n)} {w w' : ZMod n} (hw' : w' ∈ W) {j j' : ℕ}
    (hj : j < gap W w) (hle : j' ≤ j)
    (h : w + (j : ZMod n) = w' + (j' : ZMod n)) : w = w' := by
  have key : w' = w + ((j - j' : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hle]
    linear_combination -1 * h
  rcases Nat.eq_zero_or_pos (j - j') with h0 | h0
  · rw [key, h0]; simp
  · exact absurd (key ▸ hw') (not_mem_of_lt_gap h0 (by omega))

omit [NeZero n] in
/-- Arcs of distinct elements of `W` are disjoint. -/
lemma arc_disjoint {W : Finset (ZMod n)} {w w' : ZMod n} (hw : w ∈ W) (hw' : w' ∈ W)
    {x : ZMod n} (hx : x ∈ seg w (gap W w)) (hx' : x ∈ seg w' (gap W w')) : w = w' := by
  obtain ⟨j, hj, rfl⟩ := mem_seg.1 hx
  obtain ⟨j', hj', h⟩ := mem_seg.1 hx'
  rcases le_total j' j with hle | hle
  · exact arc_eq_aux hw' hj hle h
  · exact (arc_eq_aux hw hj' hle h.symm).symm

/-- The arcs of `W` partition `ZMod n`, so the gaps sum to `n`. -/
lemma sum_gap {W : Finset (ZMod n)} (hW : W.Nonempty) : ∑ w ∈ W, gap W w = n := by
  classical
  have hdisj : (W : Set (ZMod n)).PairwiseDisjoint (fun w => seg w (gap W w)) := by
    intro w hw w' hw' hne
    exact Finset.disjoint_left.2 fun x hx hx' =>
      hne (arc_disjoint (Finset.mem_coe.1 hw) (Finset.mem_coe.1 hw') hx hx')
  have hcover : W.biUnion (fun w => seg w (gap W w)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rw [Finset.mem_biUnion]
    obtain ⟨w, hw, j, hj, rfl⟩ := arc_cover hW x
    exact ⟨w, hw, mem_seg.2 ⟨j, hj, rfl⟩⟩
  calc ∑ w ∈ W, gap W w = ∑ w ∈ W, (seg w (gap W w)).card :=
        Finset.sum_congr rfl fun w _ => (seg_card (gap_le W w)).symm
    _ = n := by
        rw [← Finset.card_biUnion hdisj, hcover, Finset.card_univ, ZMod.card]

/-- `fatten W D` is `W + {0, …, D-1}`. -/
def fatten (W : Finset (ZMod n)) (D : ℕ) : Finset (ZMod n) :=
  W.biUnion (fun w => seg w D)

omit [NeZero n] in
lemma mem_fatten {W : Finset (ZMod n)} {D : ℕ} {x : ZMod n} :
    x ∈ fatten W D ↔ ∃ w ∈ W, ∃ t : ℕ, t < D ∧ x = w + (t : ZMod n) := by
  simp only [fatten, Finset.mem_biUnion, mem_seg]

omit [NeZero n] in
/-- The fattened set meets the arc of `w` in exactly its first `min (gap W w) D` elements. -/
lemma fatten_inter_arc {W : Finset (ZMod n)} {D : ℕ} {w : ZMod n} (hw : w ∈ W) :
    fatten W D ∩ seg w (gap W w) = seg w (min (gap W w) D) := by
  ext x
  simp only [Finset.mem_inter, mem_fatten, mem_seg]
  constructor
  · rintro ⟨⟨w', hw', t, ht, hxt⟩, j, hj, rfl⟩
    refine ⟨j, ?_, rfl⟩
    rw [lt_min_iff]
    refine ⟨hj, ?_⟩
    rcases Nat.lt_or_ge j D with hjD | hDj
    · exact hjD
    · exfalso
      have htj : t < j := lt_of_lt_of_le ht hDj
      have heq : w + (j : ZMod n) = w' + (t : ZMod n) := hxt
      have key : w' = w + ((j - t : ℕ) : ZMod n) := by
        rw [Nat.cast_sub (le_of_lt htj)]
        linear_combination -1 * heq
      rw [key] at hw'
      exact not_mem_of_lt_gap (j := j - t) (by omega) (by omega) hw'
  · rintro ⟨j, hj, rfl⟩
    rw [lt_min_iff] at hj
    exact ⟨⟨w, hw, j, hj.2, rfl⟩, j, hj.1, rfl⟩

/-- THE FATTENING LEMMA: `|W + {0,…,D-1}| = ∑_{w ∈ W} min (gap w) D`. -/
lemma card_fatten {W : Finset (ZMod n)} (hW : W.Nonempty) (D : ℕ) :
    (fatten W D).card = ∑ w ∈ W, min (gap W w) D := by
  classical
  have hdecomp : fatten W D = W.biUnion (fun w => fatten W D ∩ seg w (gap W w)) := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · intro hx
      obtain ⟨w, hw, j, hj, rfl⟩ := arc_cover hW x
      exact ⟨w, hw, Finset.mem_inter.2 ⟨hx, mem_seg.2 ⟨j, hj, rfl⟩⟩⟩
    · rintro ⟨w, hw, hx⟩
      exact (Finset.mem_inter.1 hx).1
  have hdisj : (W : Set (ZMod n)).PairwiseDisjoint
      (fun w => fatten W D ∩ seg w (gap W w)) := by
    intro w hw w' hw' hne
    exact Finset.disjoint_left.2 fun x hx hx' =>
      hne (arc_disjoint (Finset.mem_coe.1 hw) (Finset.mem_coe.1 hw')
        (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx').2)
  rw [hdecomp, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [fatten_inter_arc hw, seg_card (le_trans (min_le_left _ _) (gap_le W w))]

omit [NeZero n] in
lemma card_le_sum' {s : Finset (ZMod n)} {f : ZMod n → ℕ} (h : ∀ w ∈ s, 1 ≤ f w) :
    s.card ≤ ∑ w ∈ s, f w := by
  calc s.card = ∑ _w ∈ s, 1 := Finset.card_eq_sum_ones s
    _ ≤ ∑ w ∈ s, f w := Finset.sum_le_sum h

/-- If every gap is at most `D`, the fattened set is everything. -/
lemma fatten_eq_univ {W : Finset (ZMod n)} (hW : W.Nonempty) {D : ℕ}
    (hall : ∀ w ∈ W, gap W w ≤ D) : fatten W D = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_fatten hW D, ZMod.card]
  calc ∑ w ∈ W, min (gap W w) D = ∑ w ∈ W, gap W w :=
        Finset.sum_congr rfl fun w hw => min_eq_left (hall w hw)
    _ = n := sum_gap hW

/-- One gap of size at least `D` forces `|W + I| ≥ |W| - 1 + D`. -/
lemma card_fatten_lower {W : Finset (ZMod n)} (hW : W.Nonempty) {D : ℕ} (hD : 1 ≤ D)
    {w0 : ZMod n} (hw0 : w0 ∈ W) (hgap : D ≤ gap W w0) :
    W.card - 1 + D ≤ (fatten W D).card := by
  rw [card_fatten hW D]
  have h1 : ∀ w ∈ W.erase w0, 1 ≤ min (gap W w) D := fun w _ =>
    le_min (gap_pos W w) hD
  have hsplit := Finset.add_sum_erase W (fun w => min (gap W w) D) hw0
  have h2 : W.card - 1 ≤ ∑ w ∈ W.erase w0, min (gap W w) D := by
    have := card_le_sum' h1
    rwa [Finset.card_erase_of_mem hw0] at this
  have h3 : min (gap W w0) D = D := min_eq_right hgap
  omega

/-- In the equality case, every gap other than the one big one equals `1`. -/
lemma gaps_eq_one {W : Finset (ZMod n)} (hW : W.Nonempty) {D : ℕ} (hD : 2 ≤ D)
    {w0 : ZMod n} (hw0 : w0 ∈ W) (hgap : D ≤ gap W w0)
    (hcard : (fatten W D).card ≤ W.card - 1 + D) :
    ∀ w ∈ W, w ≠ w0 → gap W w = 1 := by
  intro w hw hne
  by_contra hg1
  have hg2 : 2 ≤ gap W w := by have := gap_pos W w; omega
  have hw' : w ∈ W.erase w0 := Finset.mem_erase.2 ⟨hne, hw⟩
  have hsplit := Finset.add_sum_erase W (fun u => min (gap W u) D) hw0
  have hsplit2 := Finset.add_sum_erase (W.erase w0) (fun u => min (gap W u) D) hw'
  have h1 : ∀ u ∈ (W.erase w0).erase w, 1 ≤ min (gap W u) D := fun u _ =>
    le_min (gap_pos W u) (by omega)
  have hbound := card_le_sum' h1
  rw [Finset.card_erase_of_mem hw', Finset.card_erase_of_mem hw0] at hbound
  have hminw : 2 ≤ min (gap W w) D := le_min hg2 hD
  have hminw0 : min (gap W w0) D = D := min_eq_right hgap
  rw [card_fatten hW D] at hcard
  have hc2 : 1 ≤ (W.erase w0).card := Finset.card_pos.2 ⟨w, hw'⟩
  rw [Finset.card_erase_of_mem hw0] at hc2
  omega

/-- Rigidity: if all gaps except the one at `w0` are `1`, then `W` is the cyclic
interval starting at `w0 + gap w0` of length `|W|`. -/
lemma W_eq_seg {W : Finset (ZMod n)} (hW : W.Nonempty) {w0 : ZMod n} (hw0 : w0 ∈ W)
    (hone : ∀ w ∈ W, w ≠ w0 → gap W w = 1) :
    W = seg (w0 + (gap W w0 : ZMod n)) W.card := by
  have hsum := sum_gap hW
  have hsplit := Finset.add_sum_erase W (gap W) hw0
  have herase : ∑ w ∈ W.erase w0, gap W w = W.card - 1 := by
    have hval : ∀ w ∈ W.erase w0, gap W w = 1 := fun w hw =>
      hone w (Finset.mem_erase.1 hw).2 (Finset.mem_erase.1 hw).1
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem hw0]
  have hcard1 : 1 ≤ W.card := Finset.card_pos.2 hW
  have hcardn : W.card ≤ n := by
    have := Finset.card_le_univ W
    rwa [ZMod.card] at this
  have hg0 : gap W w0 + (W.card - 1) = n := by omega
  have hstep : ∀ j : ℕ, j < W.card → w0 + (gap W w0 : ZMod n) + (j : ZMod n) ∈ W := by
    intro j
    induction j with
    | zero => intro _; simpa using add_gap_mem hw0
    | succ k ih =>
      intro hk1
      have hkW := ih (by omega)
      have hne : w0 + (gap W w0 : ZMod n) + (k : ZMod n) ≠ w0 := by
        intro heq
        have hzero : ((gap W w0 + k : ℕ) : ZMod n) = 0 := by
          push_cast
          linear_combination heq
        rw [ZMod.natCast_eq_zero_iff] at hzero
        have hgpos := gap_pos W w0
        have hlt : gap W w0 + k < n := by omega
        exact absurd (Nat.le_of_dvd (by omega) hzero) (by omega)
      have hgap1 := hone _ hkW hne
      have hmem := add_gap_mem hkW
      rw [hgap1] at hmem
      have : w0 + (gap W w0 : ZMod n) + ((k + 1 : ℕ) : ZMod n) ∈ W := by
        push_cast
        push_cast at hmem
        convert hmem using 1
        ring
      exact this
  have hseg : seg (w0 + (gap W w0 : ZMod n)) W.card ⊆ W := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_seg.1 hx
    exact hstep j hj
  exact (Finset.eq_of_subset_of_card_le hseg (seg_card hcardn).ge).symm

omit [NeZero n] in
/-- Fattening an interval gives an interval. -/
lemma fatten_seg {w0 : ZMod n} {α D : ℕ} (hα : 0 < α) (hD : 0 < D) :
    fatten (seg w0 α) D = seg w0 (α + D - 1) := by
  ext x
  rw [mem_fatten, mem_seg]
  constructor
  · rintro ⟨w, hw, t, ht, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_seg.1 hw
    refine ⟨j + t, by omega, ?_⟩
    push_cast
    ring
  · rintro ⟨s, hs, rfl⟩
    refine ⟨w0 + ((min s (α - 1) : ℕ) : ZMod n), mem_seg.2 ⟨min s (α - 1), by omega, rfl⟩,
      s - min s (α - 1), by omega, ?_⟩
    have hsplit : min s (α - 1) + (s - min s (α - 1)) = s := by omega
    calc w0 + (s : ZMod n)
        = w0 + ((min s (α - 1) + (s - min s (α - 1)) : ℕ) : ZMod n) := by rw [hsplit]
      _ = w0 + ((min s (α - 1) : ℕ) : ZMod n) + ((s - min s (α - 1) : ℕ) : ZMod n) := by
          push_cast
          ring

end Gaps

/-! ### The two core counting arguments -/

section Core

variable {n D : ℕ} [NeZero n]

omit [NeZero n] in
lemma double_inj {u : ZMod n} (hu : 2 * u = 1) {x y : ZMod n} (h : 2 * x = 2 * y) :
    x = y := by
  have hx : ∀ z : ZMod n, u * (2 * z) = z := by
    intro z
    rw [← mul_assoc, mul_comm u 2, hu, one_mul]
  calc x = u * (2 * x) := (hx x).symm
    _ = u * (2 * y) := by rw [h]
    _ = y := hx y

omit [NeZero n] in
/-- Shared setup: `2·(fatten W D) ⊆ A ∪ Xf` where `W = -u·A`. -/
lemma himg_lemma {u : ZMod n} (hu : 2 * u = 1) {A Xf : Finset (ZMod n)}
    (hstep : ∀ a ∈ A, ∀ t : ℕ, t < D →
      (2 * (t : ZMod n) - a) ∈ A ∨ (2 * (t : ZMod n) - a) ∈ Xf) :
    ∀ x ∈ fatten (A.image (fun a => -(u * a))) D, (2 * x) ∈ A ∪ Xf := by
  have hua : ∀ a : ZMod n, 2 * (u * a) = a := fun a => by
    rw [← mul_assoc, hu, one_mul]
  intro x hx
  obtain ⟨w, hw, t, ht, rfl⟩ := mem_fatten.1 hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
  have h2x : 2 * (-(u * a) + (t : ZMod n)) = 2 * (t : ZMod n) - a := by
    have h := hua a
    linear_combination -1 * h
  rw [h2x]
  rcases hstep a ha t ht with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

omit [NeZero n] in
/-- Shared setup: the cardinality bound `|fatten W D| ≤ |A| + |Xf|`. -/
lemma hbound_lemma {u : ZMod n} (hu : 2 * u = 1) {A Xf : Finset (ZMod n)}
    (hstep : ∀ a ∈ A, ∀ t : ℕ, t < D →
      (2 * (t : ZMod n) - a) ∈ A ∨ (2 * (t : ZMod n) - a) ∈ Xf) :
    (fatten (A.image (fun a => -(u * a))) D).card ≤ A.card + Xf.card := by
  classical
  set W := A.image (fun a => -(u * a)) with hWdef
  have hinj : Set.InjOn (fun x : ZMod n => 2 * x) (fatten W D) :=
    fun x _ y _ h => double_inj hu h
  have hcardimg := Finset.card_image_of_injOn hinj
  have hsub : (fatten W D).image (fun x => 2 * x) ⊆ A ∪ Xf := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact himg_lemma hu hstep x hx
  calc (fatten W D).card = ((fatten W D).image (fun x => 2 * x)).card := hcardimg.symm
    _ ≤ (A ∪ Xf).card := Finset.card_le_card hsub
    _ ≤ A.card + Xf.card := Finset.card_union_le _ _

omit [NeZero n] in
lemma cardW_lemma {u : ZMod n} (hu : 2 * u = 1) {A : Finset (ZMod n)} :
    (A.image (fun a => -(u * a))).card = A.card := by
  have hua : ∀ a : ZMod n, 2 * (u * a) = a := fun a => by
    rw [← mul_assoc, hu, one_mul]
  apply Finset.card_image_of_injOn
  intro a _ b _ h
  have h' : u * a = u * b := neg_inj.mp h
  have h2 := congrArg (fun z => 2 * z) h'
  simpa [hua] using h2

/-- Core counting argument, case `∞ ∈ X`: a closed nonempty set of finite survivors
avoiding a survivor `c0`, with at most `D - 2` finite deletions, is impossible. -/
theorem coreInf (hD2 : 2 ≤ D) (u : ZMod n) (hu : 2 * u = 1)
    (A Xf : Finset (ZMod n)) (hA : A.Nonempty) (hXf : Xf.card + 2 ≤ D)
    (hstep : ∀ a ∈ A, ∀ t : ℕ, t < D →
      (2 * (t : ZMod n) - a) ∈ A ∨ (2 * (t : ZMod n) - a) ∈ Xf)
    (c0 : ZMod n) (hc0A : c0 ∉ A) (hc0X : c0 ∉ Xf) : False := by
  classical
  set W := A.image (fun a => -(u * a)) with hWdef
  have hua : ∀ a : ZMod n, 2 * (u * a) = a := fun a => by
    rw [← mul_assoc, hu, one_mul]
  have hWne : W.Nonempty := hA.image _
  have hbound := hbound_lemma hu hstep
  rw [← hWdef] at hbound
  by_cases hex : ∃ w ∈ W, D < gap W w
  · obtain ⟨w0, hw0, hgap⟩ := hex
    have hlow := card_fatten_lower hWne (by omega) hw0 (le_of_lt hgap)
    have hcardW : W.card = A.card := cardW_lemma hu
    have hA1 : 1 ≤ A.card := Finset.card_pos.2 hA
    omega
  · have huniv : ∀ w ∈ W, gap W w ≤ D := by
      intro w hw
      rcases Nat.lt_or_ge D (gap W w) with h | h
      · exact absurd ⟨w, hw, h⟩ hex
      · exact h
    have huf := fatten_eq_univ hWne huniv
    have hc0 : c0 ∈ A ∪ Xf := by
      have hx : u * c0 ∈ fatten W D := by
        rw [huf]; exact Finset.mem_univ _
      have := himg_lemma hu hstep (u * c0) (by rw [← hWdef] at *; exact hx)
      rwa [hua c0] at this
    rcases Finset.mem_union.1 hc0 with h | h
    · exact hc0A h
    · exact hc0X h

/-- Core counting argument, case `∞ ∉ X`: a closed nonempty set of finite survivors,
none adjacent to `∞` (i.e. avoiding `{0,…,D-1}`), with at most `D - 1` finite deletions,
is impossible. This is the rigidity + parity endgame. -/
theorem coreFin (hD2 : 2 ≤ D) (hDn : D ≤ n) (u : ZMod n) (hu : 2 * u = 1)
    (A Xf : Finset (ZMod n)) (hA : A.Nonempty) (hXf : Xf.card + 1 ≤ D)
    (hstep : ∀ a ∈ A, ∀ t : ℕ, t < D →
      (2 * (t : ZMod n) - a) ∈ A ∨ (2 * (t : ZMod n) - a) ∈ Xf)
    (hAI : ∀ t : ℕ, t < D → ((t : ZMod n)) ∉ A) : False := by
  classical
  set W := A.image (fun a => -(u * a)) with hWdef
  have hua : ∀ a : ZMod n, 2 * (u * a) = a := fun a => by
    rw [← mul_assoc, hu, one_mul]
  have hWne : W.Nonempty := hA.image _
  have hbound := hbound_lemma hu hstep
  rw [← hWdef] at hbound
  have hcardW : W.card = A.card := cardW_lemma hu
  have hA1 : 1 ≤ A.card := Finset.card_pos.2 hA
  by_cases hex : ∃ w ∈ W, D < gap W w
  swap
  · -- all gaps ≤ D: the fattened set is everything, so I ⊆ Xf, contradiction
    have huniv : ∀ w ∈ W, gap W w ≤ D := by
      intro w hw
      rcases Nat.lt_or_ge D (gap W w) with h | h
      · exact absurd ⟨w, hw, h⟩ hex
      · exact h
    have huf := fatten_eq_univ hWne huniv
    have hIX : ∀ t : ℕ, t < D → (t : ZMod n) ∈ Xf := by
      intro t ht
      have hx : u * (t : ZMod n) ∈ fatten W D := by
        rw [huf]; exact Finset.mem_univ _
      have := himg_lemma hu hstep (u * (t : ZMod n)) (by rw [← hWdef] at *; exact hx)
      rw [hua] at this
      rcases Finset.mem_union.1 this with h | h
      · exact absurd h (hAI t ht)
      · exact h
    have hsub : (Finset.range D).image (fun t : ℕ => (t : ZMod n)) ⊆ Xf := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact hIX t (Finset.mem_range.1 ht)
    have hcardI : ((Finset.range D).image (fun t : ℕ => (t : ZMod n))).card = D := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro j hj k hk h
      simp only [Finset.coe_range, Set.mem_Iio] at hj hk
      exact cast_inj_of_lt (lt_of_lt_of_le hj hDn) (lt_of_lt_of_le hk hDn) h
    have := Finset.card_le_card hsub
    omega
  · -- the equality/rigidity case
    obtain ⟨w0, hw0, hgapD⟩ := hex
    have hgap : D ≤ gap W w0 := le_of_lt hgapD
    have hlow := card_fatten_lower hWne (by omega) hw0 hgap
    -- exact count
    have hone : ∀ w ∈ W, w ≠ w0 → gap W w = 1 :=
      gaps_eq_one hWne hD2 hw0 hgap (by omega)
    have hWseg := W_eq_seg hWne hw0 hone
    -- gap sum: gap w0 + (α - 1) = n, so α + D - 1 < n
    have hsum := sum_gap hWne
    have hsplit := Finset.add_sum_erase W (gap W) hw0
    have herase : ∑ w ∈ W.erase w0, gap W w = W.card - 1 := by
      have hval : ∀ w ∈ W.erase w0, gap W w = 1 := fun w hw =>
        hone w (Finset.mem_erase.1 hw).2 (Finset.mem_erase.1 hw).1
      rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hw0]
    have hstrict : A.card + D - 1 < n := by omega
    -- fatten W D is the interval starting at ws of length α + D - 1
    have hfs : fatten W D = seg (w0 + ((gap W w0 : ℕ) : ZMod n)) (A.card + D - 1) := by
      conv_lhs => rw [hWseg]
      rw [hcardW] at hWseg ⊢
      exact fatten_seg (by omega) (by omega)
    -- equality of image with A ∪ Xf
    have hinj : Set.InjOn (fun x : ZMod n => 2 * x) (fatten W D) :=
      fun x _ y _ h => double_inj hu h
    have hcardimg := Finset.card_image_of_injOn hinj
    have hsubimg : (fatten W D).image (fun x => 2 * x) ⊆ A ∪ Xf := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact himg_lemma hu hstep x (by rw [← hWdef] at *; exact hx)
    have hcf : (fatten W D).card = A.card - 1 + D := by
      rw [hfs, seg_card (by omega)]
      omega
    have himg_eq : (fatten W D).image (fun x => 2 * x) = A ∪ Xf := by
      apply Finset.eq_of_subset_of_card_le hsubimg
      have := Finset.card_union_le A Xf
      omega
    have hAsub : A ⊆ (fatten W D).image (fun x => 2 * x) := by
      rw [himg_eq]
      exact Finset.subset_union_left
    -- notation for the interval start and the base element of A
    set ws : ZMod n := w0 + ((gap W w0 : ℕ) : ZMod n) with hwsdef
    set a0 : ZMod n := -(2 * ws) with ha0def
    -- membership characterization of A
    have hmemA : ∀ a : ZMod n, a ∈ A ↔
        ∃ j : ℕ, j < A.card ∧ a = a0 - ((2 * j : ℕ) : ZMod n) := by
      intro a
      have hAW : a ∈ A ↔ -(u * a) ∈ W := by
        constructor
        · intro ha
          exact hWdef ▸ Finset.mem_image_of_mem _ ha
        · intro ha
          rw [hWdef] at ha
          obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 ha
          have h' : u * b = u * a := neg_inj.mp hba
          have h2 := congrArg (fun z => 2 * z) h'
          simp only [hua] at h2
          rwa [← h2]
      rw [hAW, hWseg, hcardW, mem_seg]
      constructor
      · rintro ⟨j, hj, hj2⟩
        refine ⟨j, hj, ?_⟩
        push_cast
        linear_combination (-2 : ZMod n) * hj2 - hua a
      · rintro ⟨j, hj, hj2⟩
        refine ⟨j, hj, ?_⟩
        push_cast at hj2
        linear_combination (-u) * hj2 + (ws + (j : ZMod n)) * hu
    -- a0 ∈ A
    have ha0A : a0 ∈ A := by
      rw [hmemA]
      exact ⟨0, by omega, by push_cast; ring⟩
    -- the value ρ = a0.val satisfies ρ ≤ α + D - 2
    have hρbound : a0.val ≤ A.card + D - 2 := by
      obtain ⟨x, hx, h2x⟩ := Finset.mem_image.1 (hAsub ha0A)
      have hxws : x = -ws := by
        apply double_inj hu
        rw [h2x, ha0def]
        ring
      rw [hxws, hfs] at hx
      obtain ⟨s, hs, hsx⟩ := mem_seg.1 hx
      have ha0s : a0 = ((s : ℕ) : ZMod n) := by
        rw [ha0def]
        linear_combination hsx
      rw [ha0s, ZMod.val_cast_of_lt (by omega)]
      omega
    -- elements of A pinned: for j < α with 2j ≤ ρ, the value ρ - 2j is ≥ D
    have hρn : a0.val < n := ZMod.val_lt a0
    have hvalA : ∀ j : ℕ, j < A.card → 2 * j ≤ a0.val → D ≤ a0.val - 2 * j := by
      intro j hj h2j
      have heA : a0 - ((2 * j : ℕ) : ZMod n) ∈ A := (hmemA _).2 ⟨j, hj, rfl⟩
      have hvale : (a0 - ((2 * j : ℕ) : ZMod n)).val = a0.val - 2 * j := by
        conv_lhs => rw [← ZMod.natCast_zmod_val a0]
        rw [← Nat.cast_sub h2j, ZMod.val_cast_of_lt (by omega)]
      rcases Nat.lt_or_ge ((a0 - ((2 * j : ℕ) : ZMod n)).val) D with hlt | hge
      · exfalso
        apply hAI _ hlt
        rw [ZMod.natCast_zmod_val]
        exact heA
      · omega
    -- the parity endgame
    rcases Nat.lt_or_ge (a0.val / 2) A.card with hcase | hcase
    · have := hvalA (a0.val / 2) hcase (by omega)
      omega
    · have := hvalA (A.card - 1) (by omega) (by omega)
      omega

end Core

/-! ### Graph plumbing -/

lemma adj_some {M D : ℕ} {a b : ZMod (2 * M + 1)} :
    (unionGraph M D).Adj (some a) (some b) ↔
      a ≠ b ∧ ∃ t : ℕ, t < D ∧ a + b = 2 * (t : ZMod (2 * M + 1)) := by
  rw [unionGraph, SimpleGraph.fromRel_adj]
  simp only [rel, ne_eq, Option.some.injEq]
  constructor
  · rintro ⟨hne, ⟨t, ht, hab⟩ | ⟨t, ht, hab⟩⟩
    · exact ⟨hne, t, ht, hab⟩
    · exact ⟨hne, t, ht, by linear_combination hab⟩
  · rintro ⟨hne, t, ht, hab⟩
    exact ⟨hne, Or.inl ⟨t, ht, hab⟩⟩

lemma adj_none {M D : ℕ} {b : ZMod (2 * M + 1)} :
    (unionGraph M D).Adj none (some b) ↔
      ∃ t : ℕ, t < D ∧ b = (t : ZMod (2 * M + 1)) := by
  rw [unionGraph, SimpleGraph.fromRel_adj]
  simp only [rel, ne_eq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.elim
  · intro h
    exact ⟨by simp, Or.inl h⟩

/-! ### The main theorem -/

theorem proof : ∀ (M D : ℕ), 2 ≤ D → D ≤ 2 * M + 1 →
    ∀ X : Finset (V M), X.card < D →
      ((unionGraph M D).induce {v : V M | v ∉ X}).Connected := by
  intro M D hD2 hDn X hX
  classical
  have hNZ : NeZero (2 * M + 1) := ⟨by omega⟩
  -- the inverse of 2
  set u : ZMod (2 * M + 1) := ((M + 1 : ℕ) : ZMod (2 * M + 1)) with hudef
  have hu : 2 * u = 1 := by
    have hself := ZMod.natCast_self (2 * M + 1)
    rw [hudef]
    push_cast at hself ⊢
    linear_combination hself
  -- the deleted finite vertices
  set Xf : Finset (ZMod (2 * M + 1)) :=
    Finset.univ.filter (fun a => some a ∈ X) with hXfdef
  have hXfmem : ∀ a : ZMod (2 * M + 1), a ∈ Xf ↔ some a ∈ X := by
    intro a
    rw [hXfdef, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  have hXfcard : Xf.card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (fun a => some a)
    · intro a ha
      exact (hXfmem a).1 ha
    · intro a _ b _ h
      exact Option.some.inj h
  -- a survivor exists
  obtain ⟨v0, hv0⟩ : ∃ v : V M, v ∉ X := by
    by_contra hcon
    have hall : ∀ v : V M, v ∈ X := by
      intro v
      by_contra hv
      exact hcon ⟨v, hv⟩
    have hle : Finset.univ.card ≤ X.card := Finset.card_le_card fun v _ => hall v
    rw [Finset.card_univ] at hle
    have hcV : Fintype.card (V M) = 2 * M + 2 := by
      rw [Fintype.card_option, ZMod.card]
    omega
  set S : Set (V M) := {v : V M | v ∉ X} with hSdef
  set G' : SimpleGraph S := (unionGraph M D).induce S with hG'def
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  -- reachability is closed under surviving edges
  have hreach_closed : ∀ (base : S) (a b : ZMod (2 * M + 1))
      (ha : (some a : V M) ∉ X) (hb : (some b : V M) ∉ X),
      (unionGraph M D).Adj (some a) (some b) →
      ¬ G'.Reachable ⟨some a, ha⟩ base → ¬ G'.Reachable ⟨some b, hb⟩ base := by
    intro base a b ha hb hadj hnr hr
    exact hnr ((SimpleGraph.Adj.reachable (by exact hadj)).trans hr)
  by_cases hinf : (none : V M) ∈ X
  · -- CASE ∞ deleted: base at an arbitrary (necessarily finite) survivor
    obtain ⟨c0, rfl⟩ : ∃ c, v0 = some c := by
      cases v0 with
      | none => exact absurd hinf hv0
      | some c => exact ⟨c, rfl⟩
    refine ⟨⟨some c0, hv0⟩, ?_⟩
    intro w
    rcases w with ⟨wv, hwS⟩
    obtain ⟨b0, rfl⟩ : ∃ c, wv = some c := by
      cases wv with
      | none => exact absurd hinf hwS
      | some c => exact ⟨c, rfl⟩
    by_contra hw
    set base : S := ⟨some c0, hv0⟩ with hbasedef
    set A : Finset (ZMod (2 * M + 1)) :=
      Finset.univ.filter
        (fun a => ∃ h : (some a : V M) ∉ X, ¬ G'.Reachable ⟨some a, h⟩ base) with hAdef
    have hAmem : ∀ a : ZMod (2 * M + 1), a ∈ A ↔
        ∃ h : (some a : V M) ∉ X, ¬ G'.Reachable ⟨some a, h⟩ base := by
      intro a
      rw [hAdef, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
    have hAne : A.Nonempty := ⟨b0, (hAmem b0).2 ⟨hwS, fun hr => hw hr.symm⟩⟩
    have hstep : ∀ a ∈ A, ∀ t : ℕ, t < D →
        (2 * (t : ZMod (2 * M + 1)) - a) ∈ A ∨ (2 * (t : ZMod (2 * M + 1)) - a) ∈ Xf := by
      intro a ha t ht
      obtain ⟨haX, hnr⟩ := (hAmem a).1 ha
      by_cases hbX : (some (2 * (t : ZMod (2 * M + 1)) - a) : V M) ∈ X
      · exact Or.inr ((hXfmem _).2 hbX)
      · left
        rw [hAmem]
        refine ⟨hbX, ?_⟩
        by_cases hab : a = 2 * (t : ZMod (2 * M + 1)) - a
        · intro hr
          apply hnr
          have heq : (⟨some a, haX⟩ : S) = ⟨some (2 * (t : ZMod (2 * M + 1)) - a), hbX⟩ :=
            Subtype.ext (congrArg some hab)
          rw [heq]
          exact hr
        · have hadj : (unionGraph M D).Adj (some a)
              (some (2 * (t : ZMod (2 * M + 1)) - a)) := by
            rw [adj_some]
            exact ⟨hab, t, ht, by ring⟩
          exact hreach_closed base a _ haX hbX hadj hnr
    have hc0A : c0 ∉ A := by
      intro hin
      obtain ⟨haX, hnr⟩ := (hAmem _).1 hin
      apply hnr
      have heq : (⟨some c0, haX⟩ : S) = base := Subtype.ext rfl
      rw [heq]
    have hc0X : c0 ∉ Xf := fun h => hv0 ((hXfmem c0).1 h)
    have hXfcard2 : Xf.card + 1 ≤ X.card := by
      have hsub : Xf.image (fun a => (some a : V M)) ⊆ X.erase none := by
        intro y hy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
        exact Finset.mem_erase.2 ⟨by simp, (hXfmem a).1 ha⟩
      have hinj : (Xf.image (fun a => (some a : V M))).card = Xf.card :=
        Finset.card_image_of_injOn fun a _ b _ h => Option.some.inj h
      have hle := Finset.card_le_card hsub
      rw [hinj, Finset.card_erase_of_mem hinf] at hle
      have hX1 : 1 ≤ X.card := Finset.card_pos.2 ⟨none, hinf⟩
      omega
    have hXfD : Xf.card + 2 ≤ D := by omega
    exact coreInf hD2 u hu A Xf hAne hXfD hstep c0 hc0A hc0X
  · -- CASE ∞ survives: base at ∞
    refine ⟨⟨none, hinf⟩, ?_⟩
    intro w
    rcases w with ⟨wv, hwS⟩
    cases wv with
    | none =>
      have heq : (⟨none, hwS⟩ : S) = ⟨none, hinf⟩ := Subtype.ext rfl
      rw [heq]
    | some b0 =>
      by_contra hw
      set base : S := ⟨none, hinf⟩ with hbasedef
      set A : Finset (ZMod (2 * M + 1)) :=
        Finset.univ.filter
          (fun a => ∃ h : (some a : V M) ∉ X, ¬ G'.Reachable ⟨some a, h⟩ base) with hAdef
      have hAmem : ∀ a : ZMod (2 * M + 1), a ∈ A ↔
          ∃ h : (some a : V M) ∉ X, ¬ G'.Reachable ⟨some a, h⟩ base := by
        intro a
        rw [hAdef, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
      have hAne : A.Nonempty := ⟨b0, (hAmem b0).2 ⟨hwS, fun hr => hw hr.symm⟩⟩
      have hstep : ∀ a ∈ A, ∀ t : ℕ, t < D →
          (2 * (t : ZMod (2 * M + 1)) - a) ∈ A ∨ (2 * (t : ZMod (2 * M + 1)) - a) ∈ Xf := by
        intro a ha t ht
        obtain ⟨haX, hnr⟩ := (hAmem a).1 ha
        by_cases hbX : (some (2 * (t : ZMod (2 * M + 1)) - a) : V M) ∈ X
        · exact Or.inr ((hXfmem _).2 hbX)
        · left
          rw [hAmem]
          refine ⟨hbX, ?_⟩
          by_cases hab : a = 2 * (t : ZMod (2 * M + 1)) - a
          · intro hr
            apply hnr
            have heq : (⟨some a, haX⟩ : S) = ⟨some (2 * (t : ZMod (2 * M + 1)) - a), hbX⟩ :=
              Subtype.ext (congrArg some hab)
            rw [heq]
            exact hr
          · have hadj : (unionGraph M D).Adj (some a)
                (some (2 * (t : ZMod (2 * M + 1)) - a)) := by
              rw [adj_some]
              exact ⟨hab, t, ht, by ring⟩
            exact hreach_closed base a _ haX hbX hadj hnr
      have hAI : ∀ t : ℕ, t < D → ((t : ZMod (2 * M + 1))) ∉ A := by
        intro t ht hin
        obtain ⟨haX, hnr⟩ := (hAmem _).1 hin
        apply hnr
        have hadj : (unionGraph M D).Adj none (some ((t : ZMod (2 * M + 1)))) := by
          rw [adj_none]
          exact ⟨t, ht, rfl⟩
        have hadj' : G'.Adj ⟨some ((t : ZMod (2 * M + 1))), haX⟩ base := by
          exact hadj.symm
        exact hadj'.reachable
      exact coreFin hD2 (by omega) u hu A Xf hAne (by omega) hstep hAI

end Submissions.RoundRobinUnionConnectivity.RoundRobinConn
