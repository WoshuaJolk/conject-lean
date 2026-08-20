import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace Submissions.MinUPB224kMinus1Lower.Parity

open Finset

/-- The Hermitian pairing, conjugate-linear in the first slot. -/
def ip {d : ℕ} (x y : Fin d → ℂ) : ℂ := ∑ r, star (x r) * y r

lemma ip_conj {d : ℕ} (x y : Fin d → ℂ) : star (ip x y) = ip y x := by
  simp [ip, star_sum, mul_comm]

lemma ip_eq_zero_comm {d : ℕ} {x y : Fin d → ℂ} : ip x y = 0 ↔ ip y x = 0 := by
  constructor <;> intro h
  · rw [← ip_conj, h, star_zero]
  · rw [← ip_conj, h, star_zero]

lemma ip_self_ne_zero {d : ℕ} {x : Fin d → ℂ} (hx : x ≠ 0) : ip x x ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r, x r ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have key : ∀ r : Fin d, star (x r) * x r = ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have h := RCLike.conj_mul (K := ℂ) (x r)
    push_cast
    simpa using h
  have hsum : ip x x = ((∑ r, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  rw [hsum]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => sq_nonneg ‖x r‖)).1 hzero
  have hn : ‖x r₀‖ = 0 := by
    have h2 := hall r₀ (Finset.mem_univ r₀)
    nlinarith [norm_nonneg (x r₀)]
  exact hr₀ (norm_eq_zero.1 hn)

/-- Every nonzero vector of `C²` has a nonzero orthogonal partner. -/
lemma exists_perp2 {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ∃ a : Fin 2 → ℂ, a ≠ 0 ∧ ip v a = 0 := by
  refine ⟨![- star (v 1), star (v 0)], ?_, ?_⟩
  · intro h
    apply hv
    have h0 : (- star (v 1) : ℂ) = 0 := by
      have := congrFun h 0; simpa using this
    have h1 : (star (v 0) : ℂ) = 0 := by
      have := congrFun h 1; simpa using this
    funext r
    fin_cases r
    · simpa using congrArg star h1
    · have : star (v 1) = (0 : ℂ) := by simpa using neg_eq_zero.1 h0
      simpa using congrArg star this
  · simp [ip, Fin.sum_univ_two]
    ring

/-- Pairing against a finite family of vectors, as a `ℂ`-linear map. Linearity is in the
second slot, which carries no `star`. -/
def ipMap {d m : ℕ} (z : Fin m → Fin d → ℂ) (T : Finset (Fin m)) :
    (Fin d → ℂ) →ₗ[ℂ] (T → ℂ) where
  toFun c := fun l => ip (z l.1) c
  map_add' c c' := by
    funext l; simp [ip, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext l; simp [ip, Finset.mul_sum, mul_left_comm]

/-- Fewer than `d` linear conditions on `C^d` always leave a nonzero solution. -/
lemma exists_kernel_vec {d m : ℕ} (z : Fin m → Fin d → ℂ) (T : Finset (Fin m))
    (hcard : T.card < d) :
    ∃ c : Fin d → ℂ, c ≠ 0 ∧ ∀ l ∈ T, ip (z l) c = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (ipMap z T) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hne
    obtain ⟨l, hlT, hl⟩ := hcon c hne
    have : (ipMap z T) c ⟨l, hlT⟩ = 0 := by
      rw [LinearMap.mem_ker] at hc; rw [hc]; rfl
    exact hl this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
  omega

/-- A fixed-point-free involution forces even cardinality. -/
lemma even_card_of_involutive {α : Type*} [DecidableEq α] (f : α → α)
    (hff : ∀ x, f (f x) = x) (hne : ∀ x, f x ≠ x) :
    ∀ s : Finset α, (∀ x ∈ s, f x ∈ s) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hcl
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hfa : f a ∈ s := hcl a ha
      have hfa' : f a ∈ s.erase a := Finset.mem_erase.2 ⟨hne a, hfa⟩
      set t := (s.erase a).erase (f a) with ht
      have hts : t ⊆ s :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hat : a ∉ t := by
        simp [ht, Finset.mem_erase]
      have hsub : t ⊂ s := ⟨hts, fun h => hat (h ha)⟩
      have hclt : ∀ x ∈ t, f x ∈ t := by
        intro x hx
        rw [ht, Finset.mem_erase, Finset.mem_erase] at hx
        obtain ⟨hxfa, hxa, hxs⟩ := hx
        rw [ht, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hcl x hxs⟩
        · intro h
          exact hxa (by rw [← hff x, h, hff a])
        · intro h
          exact hxfa (by rw [← hff x, h])
      have hev := ih t hsub hclt
      have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      have h2 : t.card = (s.erase a).card - 1 := Finset.card_erase_of_mem hfa'
      have hs1 : 1 ≤ s.card := Finset.card_pos.2 ⟨a, ha⟩
      have hs2 : 1 ≤ (s.erase a).card := Finset.card_pos.2 ⟨f a, hfa'⟩
      have : s.card = t.card + 2 := by omega
      rw [this]
      exact hev.add (even_two)

/-- **The lower bound, in the form that matters.**

If `d` is odd and at least `3`, there is no unextendible orthogonal product set of any
cardinality `m ≤ d + 2` in `C² ⊗ C² ⊗ C^d`. Specialised at `d = 4k-1` this is exactly
Alon–Lovász Cor. 4.1(i) for the family `(2,2,4k-1)`, proved here without their Theorem 3.1:
because `d₁ = d₂ = 2`, the "exactly `dⱼ - 1` edges of colour `j` at each vertex" structure
that they extract from connectivity of the orthogonal representation follows instead from a
direct count. -/
theorem no_upb_of_odd {d m : ℕ} (hd : 3 ≤ d) (hm : m ≤ d + 2) (hdodd : ¬ Even (d + 2))
    (u : Fin m → Fin 2 → ℂ) (w : Fin m → Fin 2 → ℂ) (z : Fin m → Fin d → ℂ)
    (hu : ∀ i, u i ≠ 0) (hw : ∀ i, w i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (horth : ∀ i j, i ≠ j → ip (u i) (u j) * ip (w i) (w j) * ip (z i) (z j) = 0)
    (hunext : ∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
      ∀ c : Fin d → ℂ, c ≠ 0 → ∃ i, ip (u i) a * ip (w i) b * ip (z i) c ≠ 0) :
    False := by
  classical
  -- A convenient nonzero vector of `C²`.
  have hone : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  -- Step A: at least `d` states.
  have hmd : d ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hcard : (Finset.univ : Finset (Fin m)).card < d := by
      simpa [Finset.card_univ] using hlt
    obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z Finset.univ hcard
    obtain ⟨i, hi⟩ := hunext _ hone _ hone c hc0
    exact hi (by rw [hc i (Finset.mem_univ i), mul_zero])
  have hm3 : 3 ≤ m := le_trans hd hmd
  -- Step C: for every nonzero `a`, at most one state is killed by `a` on the first factor.
  have hAcard : ∀ a : Fin 2 → ℂ, a ≠ 0 →
      (Finset.univ.filter (fun l => ip (u l) a = 0)).card ≤ 1 := by
    intro a ha
    by_contra hgt
    push_neg at hgt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hgt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    -- a third index, distinct from both
    have hcard2 : ({p, q} : Finset (Fin m)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have hss : ({p, q} : Finset (Fin m)) ⊂ Finset.univ := by
      rw [Finset.ssubset_univ_iff]
      intro h
      rw [h, Finset.card_univ, Fintype.card_fin] at hcard2
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_of_ssubset hss
    have hjp : j ≠ p := by intro h; exact hj (by simp [h])
    have hjq : j ≠ q := by intro h; exact hj (by simp [h])
    obtain ⟨b, hb0, hb⟩ := exists_perp2 (hw j)
    -- everything outside `{p, q, j}` is too small to pin down a `c`
    set T : Finset (Fin m) := ((Finset.univ.erase p).erase q).erase j with hT
    have hcardT : T.card < d := by
      have e1 : (Finset.univ.erase p).card = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ p)]; simp
      have e2 : ((Finset.univ.erase p).erase q).card = m - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩), e1]
        omega
      have e3 : T.card = m - 3 := by
        rw [hT, Finset.card_erase_of_mem
          (Finset.mem_erase.2 ⟨hjq, Finset.mem_erase.2 ⟨hjp, Finset.mem_univ j⟩⟩), e2]
        omega
      omega
    obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z T hcardT
    obtain ⟨i, hi⟩ := hunext a ha b hb0 c hc0
    have h1 : ip (u i) a ≠ 0 := by
      intro h; exact hi (by rw [h]; ring)
    have h2 : ip (w i) b ≠ 0 := by
      intro h; exact hi (by rw [h]; ring)
    have h3 : ip (z i) c ≠ 0 := by
      intro h; exact hi (by rw [h]; ring)
    have hip : i ≠ p := by intro h; exact h1 (h ▸ hp)
    have hiq : i ≠ q := by intro h; exact h1 (h ▸ hq)
    have hij : i ≠ j := by intro h; exact h2 (h ▸ hb)
    exact h3 (hc i (by
      rw [hT]
      exact Finset.mem_erase.2 ⟨hij, Finset.mem_erase.2 ⟨hiq, Finset.mem_erase.2
        ⟨hip, Finset.mem_univ i⟩⟩⟩))
  -- Step D: the same on the second factor.
  have hBcard : ∀ b : Fin 2 → ℂ, b ≠ 0 →
      (Finset.univ.filter (fun l => ip (w l) b = 0)).card ≤ 1 := by
    intro b hb
    by_contra hgt
    push_neg at hgt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hgt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hcard2 : ({p, q} : Finset (Fin m)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have hss : ({p, q} : Finset (Fin m)) ⊂ Finset.univ := by
      rw [Finset.ssubset_univ_iff]
      intro h
      rw [h, Finset.card_univ, Fintype.card_fin] at hcard2
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_of_ssubset hss
    have hjp : j ≠ p := by intro h; exact hj (by simp [h])
    have hjq : j ≠ q := by intro h; exact hj (by simp [h])
    obtain ⟨a, ha0, ha⟩ := exists_perp2 (hu j)
    set T : Finset (Fin m) := ((Finset.univ.erase p).erase q).erase j with hT
    have hcardT : T.card < d := by
      have e1 : (Finset.univ.erase p).card = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ p)]; simp
      have e2 : ((Finset.univ.erase p).erase q).card = m - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩), e1]
        omega
      have e3 : T.card = m - 3 := by
        rw [hT, Finset.card_erase_of_mem
          (Finset.mem_erase.2 ⟨hjq, Finset.mem_erase.2 ⟨hjp, Finset.mem_univ j⟩⟩), e2]
        omega
      omega
    obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z T hcardT
    obtain ⟨i, hi⟩ := hunext a ha0 b hb c hc0
    have h1 : ip (u i) a ≠ 0 := by intro h; exact hi (by rw [h]; ring)
    have h2 : ip (w i) b ≠ 0 := by intro h; exact hi (by rw [h]; ring)
    have h3 : ip (z i) c ≠ 0 := by intro h; exact hi (by rw [h]; ring)
    have hip : i ≠ p := by intro h; exact h2 (h ▸ hp)
    have hiq : i ≠ q := by intro h; exact h2 (h ▸ hq)
    have hij : i ≠ j := by intro h; exact h1 (h ▸ ha)
    exact h3 (hc i (by
      rw [hT]
      exact Finset.mem_erase.2 ⟨hij, Finset.mem_erase.2 ⟨hiq, Finset.mem_erase.2
        ⟨hip, Finset.mem_univ i⟩⟩⟩))
  -- Chosen annihilators for each state.
  choose A hA0 hA using fun i => exists_perp2 (hu i)
  choose B hB0 hB using fun i => exists_perp2 (hw i)
  -- Step G: with `a = A i` and `b = B j` the only states that can be missed are `i` and `j`.
  have hkey : ∀ i j : Fin m, i ≠ j → ∀ c : Fin d → ℂ, c ≠ 0 →
      ∃ l, l ≠ i ∧ l ≠ j ∧ ip (z l) c ≠ 0 := by
    intro i j _ c hc0
    obtain ⟨l, hl⟩ := hunext (A i) (hA0 i) (B j) (hB0 j) c hc0
    have h1 : ip (u l) (A i) ≠ 0 := by intro h; exact hl (by rw [h]; ring)
    have h2 : ip (w l) (B j) ≠ 0 := by intro h; exact hl (by rw [h]; ring)
    have h3 : ip (z l) c ≠ 0 := by intro h; exact hl (by rw [h]; ring)
    exact ⟨l, fun h => h1 (h ▸ hA i), fun h => h2 (h ▸ hB j), h3⟩
  -- Step F: hence `m = d + 2`.
  have hmeq : m = d + 2 := by
    have h2 : 2 ≤ m := by omega
    obtain ⟨i, j, hij⟩ : ∃ i j : Fin m, i ≠ j := by
      refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
      intro h
      exact absurd (congrArg Fin.val h) (by simp)
    by_contra hlt
    have hmlt : m < d + 2 := by omega
    set T : Finset (Fin m) := (Finset.univ.erase i).erase j with hT
    have hcardT : T.card < d := by
      have e1 : (Finset.univ.erase i).card = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
      have e2 : T.card = m - 2 := by
        rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), e1]
        omega
      omega
    obtain ⟨c, hc0, hc⟩ := exists_kernel_vec z T hcardT
    obtain ⟨l, hli, hlj, hl⟩ := hkey i j hij c hc0
    exact hl (hc l (by
      rw [hT]
      exact Finset.mem_erase.2 ⟨hlj, Finset.mem_erase.2 ⟨hli, Finset.mem_univ l⟩⟩))
  -- Step H: each state is non-orthogonal to at least two others on the third factor.
  have hdeg : ∀ i : Fin m,
      ((Finset.univ.erase i).filter (fun l => ip (z i) (z l) = 0)).card ≤ m - 3 := by
    intro i
    set R := (Finset.univ.erase i).filter (fun l => ip (z i) (z l) = 0) with hR
    set N := (Finset.univ.erase i).filter (fun l => ¬ (ip (z i) (z l) = 0)) with hN
    have hNR : N = (Finset.univ.erase i) \ R := by rw [hN, hR, Finset.filter_not]
    have hRsub : R ⊆ Finset.univ.erase i := Finset.filter_subset _ _
    have hei : (Finset.univ.erase i).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
    have hsum : N.card = (m - 1) - R.card := by
      rw [hNR, Finset.card_sdiff, Finset.inter_eq_left.2 hRsub, hei]
    have hRle : R.card ≤ m - 1 := hei ▸ Finset.card_le_card hRsub
    -- at least two non-orthogonal partners
    have hN2 : 2 ≤ N.card := by
      by_contra hlt
      push_neg at hlt
      -- pick `j` covering all of `N`
      obtain ⟨j, hji, hNj⟩ : ∃ j : Fin m, j ≠ i ∧ ∀ l ∈ N, l = j := by
        rcases Finset.card_le_one.1 (by omega : N.card ≤ 1) with h
        rcases N.eq_empty_or_nonempty with he | ⟨n0, hn0⟩
        · obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i := by
            obtain ⟨x, y, hxy⟩ : ∃ x y : Fin m, x ≠ y := by
              refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
              intro hcon
              exact absurd (congrArg Fin.val hcon) (by simp)
            by_cases hx : x = i
            · exact ⟨y, fun hc => hxy (hx.trans hc.symm)⟩
            · exact ⟨x, hx⟩
          exact ⟨j, hj, fun l hl => absurd hl (by rw [he]; simp)⟩
        · refine ⟨n0, ?_, fun l hl => h l hl n0 hn0⟩
          have := Finset.mem_of_mem_filter n0 hn0
          exact (Finset.mem_erase.1 this).1
      obtain ⟨l, hli, hlj, hl⟩ := hkey i j (Ne.symm hji) (z i) (hz i)
      have : l ∈ N := by
        rw [hN, Finset.mem_filter]
        refine ⟨Finset.mem_erase.2 ⟨hli, Finset.mem_univ l⟩, ?_⟩
        intro hcon
        exact hl (ip_eq_zero_comm.1 hcon)
      exact hlj (hNj l this)
    omega
  -- Step I: each state has exactly one orthogonal partner on the FIRST factor.
  have hPone : ∀ i : Fin m,
      ((Finset.univ.erase i).filter (fun l => ip (u i) (u l) = 0)).card = 1 := by
    intro i
    set P := (Finset.univ.erase i).filter (fun l => ip (u i) (u l) = 0) with hP
    set Q := (Finset.univ.erase i).filter (fun l => ip (w i) (w l) = 0) with hQ
    set R := (Finset.univ.erase i).filter (fun l => ip (z i) (z l) = 0) with hR
    have hei : (Finset.univ.erase i).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
    -- upper bound from Step C
    have hPle : P.card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) (hAcard (u i) (hu i))
      intro l hl
      rw [hP, Finset.mem_filter] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ip_eq_zero_comm.1 hl.2
    have hQle : Q.card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) (hBcard (w i) (hw i))
      intro l hl
      rw [hQ, Finset.mem_filter] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ip_eq_zero_comm.1 hl.2
    -- the three colours cover everything
    have hcover : Finset.univ.erase i ⊆ P ∪ Q ∪ R := by
      intro l hl
      have hli : l ≠ i := (Finset.mem_erase.1 hl).1
      have := horth i l (Ne.symm hli)
      rcases mul_eq_zero.1 this with h | h3
      · rcases mul_eq_zero.1 h with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (by rw [hP, Finset.mem_filter]; exact ⟨hl, h1⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (by rw [hQ, Finset.mem_filter]; exact ⟨hl, h2⟩))
      · exact Finset.mem_union_right _ (by rw [hR, Finset.mem_filter]; exact ⟨hl, h3⟩)
    have hchain : m - 1 ≤ P.card + Q.card + R.card := by
      calc m - 1 = (Finset.univ.erase i).card := hei.symm
        _ ≤ (P ∪ Q ∪ R).card := Finset.card_le_card hcover
        _ ≤ (P ∪ Q).card + R.card := Finset.card_union_le _ _
        _ ≤ P.card + Q.card + R.card := by
            exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    have hRle := hdeg i
    rw [← hR] at hRle
    omega
  -- Step J: that partner map is a fixed-point-free involution.
  choose g hg using fun i => Finset.card_eq_one.1 (hPone i)
  have hgmem : ∀ i, g i ∈ (Finset.univ.erase i).filter (fun l => ip (u i) (u l) = 0) := by
    intro i; rw [hg i]; exact Finset.mem_singleton_self _
  have hgne : ∀ i, g i ≠ i := by
    intro i
    have := Finset.mem_of_mem_filter (g i) (hgmem i)
    exact (Finset.mem_erase.1 this).1
  have hgorth : ∀ i, ip (u i) (u (g i)) = 0 := by
    intro i
    have := (Finset.mem_filter.1 (hgmem i)).2
    exact this
  have hginv : ∀ i, g (g i) = i := by
    intro i
    have hmem : i ∈ (Finset.univ.erase (g i)).filter (fun l => ip (u (g i)) (u l) = 0) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_erase.2 ⟨Ne.symm (hgne i), Finset.mem_univ i⟩,
        ip_eq_zero_comm.1 (hgorth i)⟩
    rw [hg (g i), Finset.mem_singleton] at hmem
    exact hmem.symm
  -- Step K: so `m` is even, contradicting `m = d + 2` odd.
  have heven : Even (Finset.univ : Finset (Fin m)).card :=
    even_card_of_involutive g hginv hgne Finset.univ (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin, hmeq] at heven
  exact hdodd heven

/-- **The canonical proposition of `MinUPB224kMinus1Lower`.**

Specialising `no_upb_of_odd` at `d = 4k-1`: for `k ≥ 2` that `d` is odd and at least `3`,
and `d + 2 = 4k+1`, so no unextendible orthogonal product set of `C² ⊗ C² ⊗ C^(4k-1)` has
cardinality `m ≤ 4k+1`. Equivalently `f_m(2,2,4k-1) ≥ 4k+2`. -/
theorem proof :
    ∀ k : ℕ, 2 ≤ k → ∀ m : ℕ, m ≤ 4 * k + 1 →
      ¬ ∃ u : Fin m → Fin 2 → ℂ,
        ∃ w : Fin m → Fin 2 → ℂ,
        ∃ z : Fin m → Fin (4 * k - 1) → ℂ,
          (∀ i, u i ≠ 0) ∧
          (∀ i, w i ≠ 0) ∧
          (∀ i, z i ≠ 0) ∧
          (∀ i j, i ≠ j →
            (∑ r, star (u i r) * u j r) *
            (∑ r, star (w i r) * w j r) *
            (∑ r, star (z i r) * z j r) = 0) ∧
          (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 →
            ∀ c : Fin (4 * k - 1) → ℂ, c ≠ 0 →
            ∃ i,
              (∑ r, star (u i r) * a r) *
              (∑ r, star (w i r) * b r) *
              (∑ r, star (z i r) * c r) ≠ 0) := by
  rintro k hk m hm ⟨u, w, z, hu, hw, hz, horth, hunext⟩
  refine no_upb_of_odd (d := 4 * k - 1) (by omega) (by omega) ?_ u w z hu hw hz horth hunext
  rw [Nat.not_even_iff]
  omega

end Submissions.MinUPB224kMinus1Lower.Parity
