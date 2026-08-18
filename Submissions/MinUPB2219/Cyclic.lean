import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-!
# MinUPB2219 — an unextendible product basis of cardinality 22 in `C² ⊗ C² ⊗ C^19`

The witness is the `k = 5` member of an explicit family built by iterating a local
"block insertion" surgery on the verified `k = 2` witness. Every entry is an integer of
absolute value at most 12.

The unextendibility proof is dual. Let `Z` be the `22 × 19` integer matrix of third factors.
We supply

* `Y : Fin 3 → Fin 22 → ℤ` with `Y * Z = 0` — a basis of the space of linear relations
  among the 22 vectors (their rank is 19 = 22 − 3, so the relation space is exactly 3-dimensional);
* `L : Fin 19 → Fin 22 → ℤ` with `L * Z = 2520 * I` — an integer left inverse, so `Z` is injective.

For nonzero `a : C²` the states annihilated by `a` form a single `u`-parallel class, and for
nonzero `b : C²` a single `w`-parallel class (all of which are singletons here). Hence at most
three of the numbers `⟨zᵢ, c⟩` can be nonzero, and their index set `T` lies in
`class(k₀) ∪ {j₀}`. The three relations then read `Σ_{i ∈ T} Y r i · ⟨zᵢ, c⟩ = 0`, a
3 × 3 system whose determinant `D3` is nonzero — that is the table `hdd`, checked by `decide`.
So every `⟨zᵢ, c⟩` vanishes, and `L` forces `c = 0`.

All finite combinatorics (orthogonality of the 22 product states, `Y * Z = 0`, `L * Z = 2520 I`,
the determinant table, the covering property of the index table, and the pairwise
non-parallelism of the `u`- and `w`-directions) are integer statements closed by `decide`.
-/

namespace Submissions.MinUPB2219.Cyclic

def U : Fin 22 → Fin 2 → ℤ := ![![1, 1],
   ![1, 1],
   ![(-1), 1],
   ![(-1), 1],
   ![1, 2],
   ![1, 2],
   ![(-2), 1],
   ![(-2), 1],
   ![1, 3],
   ![(-3), 1],
   ![1, 4],
   ![1, 4],
   ![(-4), 1],
   ![(-4), 1],
   ![1, 5],
   ![1, 5],
   ![(-5), 1],
   ![(-5), 1],
   ![1, 6],
   ![1, 6],
   ![(-6), 1],
   ![(-6), 1]]

def W : Fin 22 → Fin 2 → ℤ := ![![1, 1],
   ![1, 2],
   ![1, 3],
   ![1, 4],
   ![1, 5],
   ![1, 6],
   ![1, 7],
   ![(-4), 1],
   ![(-1), 1],
   ![(-5), 1],
   ![1, 8],
   ![(-6), 1],
   ![1, 9],
   ![(-7), 1],
   ![1, 10],
   ![(-9), 1],
   ![1, 11],
   ![(-8), 1],
   ![(-2), 1],
   ![(-11), 1],
   ![(-3), 1],
   ![(-10), 1]]

def Z : Fin 22 → Fin 19 → ℤ := ![![0, 0, (-6), (-5), 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
   ![5, (-4), (-2), 0, 0, 0, 0, (-2), 12, 1, 0, (-2), (-1), 1, 0, (-2), (-1), 1, 0],
   ![0, (-3), 6, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, (-1), 1, (-6), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 2, 2, (-3), (-3), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![12, 12, 6, (-6), 6, 0, 0, (-12), (-2), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, (-2), 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, (-1), (-6), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 1, 0, 2, (-12), (-1), 2, 0, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 1, (-12), (-2), 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, (-1), 2, 0, 1],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, (-2), 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, (-2)],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def Y : Fin 3 → Fin 22 → ℤ := ![![7, (-36), 0, 5, (-39), (-8), 3, (-5), 241, 1485, 72, 14, 24, (-895), 108, (-168), (-48), (-516), 144, (-168), (-120), (-588)],
   ![56, 180, (-12), 67, (-108), 86, (-10), 101, 704, 4332, (-324), 38, 1116, 3822, (-528), (-480), 1548, (-108), (-732), (-504), 1980, 252],
   ![(-7), 144, (-12), (-5), 63, 8, (-7), 5, (-385), (-2373), (-252), 122, 1980, 2787, (-420), (-1488), 2340, (-2304), (-588), (-1512), 2700, (-2016)]]

def L : Fin 19 → Fin 22 → ℤ := ![![(-3010), 720, 240, (-3284), 8730, (-2860), 50, (-3772), (-55390), (-341070), 360, 80, 0, (-4530), 120, (-480), 0, (-1440), (-120), 0, 0, 0],
   ![(-840), 0, 0, (-924), 2520, 0, 0, (-252), (-15960), (-98280), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-420), 0, 0, (-84), 1260, 0, 0, (-252), (-7980), (-49140), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 126, (-1260), 0, 0, 378, 7560, 46620, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 126, 1260, 0, 0, 378, (-7560), (-46620), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, (-2520), (-15120), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-4480), 720, 240, (-4712), 14400, (-3280), (-160), (-4696), (-90880), (-559680), 360, 80, 0, (-4320), 120, (-480), 0, (-1440), (-120), 0, 0, 0],
   ![2520, 0, 0, 2772, (-7560), 2520, 0, 3276, 47880, 294840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![210, 0, 0, 231, (-630), 210, 0, 273, 3990, 24570, 0, (-210), 0, 420, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-2520), 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-4480), 720, 240, (-4712), 14400, (-3280), (-160), (-4696), (-90880), (-559680), (-2160), 80, 5040, 25920, 120, (-480), 0, 1080, (-120), 0, 0, 0],
   ![(-210), 0, 0, (-231), 630, (-210), 0, (-273), (-3990), (-24570), 0, 210, 2520, (-420), 0, 0, 0, 0, 0, 0, 0, 0],
   ![210, 0, 0, 231, (-630), 210, 0, 273, 3990, 24570, 0, (-210), (-2520), 420, 0, 2520, 0, 5040, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2520, 0, 0, 0, 0],
   ![11970, 360, (-720), 12708, (-37530), 9420, 270, 13164, 237150, 1460430, 1440, (-240), (-5040), (-17070), (-360), 1440, 0, 1800, 360, 0, 0, 0],
   ![(-210), 0, 0, (-231), 630, (-210), 0, (-273), (-3990), (-24570), 0, 210, 2520, (-420), 0, (-2520), 2520, (-5040), 0, 0, 0, 0],
   ![(-14210), 0, 840, (-15064), 44730, (-11060), (-350), (-15512), (-282590), (-1740270), (-2520), 280, 7560, 30030, (-840), (-1680), 2520, 0, 840, 0, 0, 0],
   ![16450, (-360), (-960), 17420, (-51930), 12700, 430, 17860, 328030, 2020110, 3600, (-320), (-10080), (-42990), 2040, 1920, (-5040), (-1800), 480, 0, 0, 0]]

def UC : Fin 12 → Fin 2 → ℤ := ![![1, 1],
   ![(-1), 1],
   ![1, 2],
   ![(-2), 1],
   ![1, 3],
   ![(-3), 1],
   ![1, 4],
   ![(-4), 1],
   ![1, 5],
   ![(-5), 1],
   ![1, 6],
   ![(-6), 1]]

def PP : Fin 12 → Fin 22 → Fin 22 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   ![0, 1, 2, 3, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
   ![0, 1, 2, 3, 4, 5, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
   ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 14, 14, 14, 14, 14, 14],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 16, 16, 16, 16],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0, 18, 18],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 0]]

def QQ : Fin 12 → Fin 22 → Fin 22 := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   ![2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
   ![4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
   ![6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
   ![1, 1, 2, 3, 4, 5, 6, 7, 1, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8],
   ![1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
   ![10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],
   ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13],
   ![14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15],
   ![16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17],
   ![18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19],
   ![20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]]

def JJ : Fin 12 → Fin 22 → Fin 22 := ![![2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![3, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![5, 5, 5, 5, 5, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![7, 7, 7, 7, 7, 7, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 15, 16, 17, 18, 19, 20, 21],
   ![15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 17, 18, 19, 20, 21],
   ![17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 19, 20, 21],
   ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 21],
   ![21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21]]

def cls : Fin 22 → Fin 12 := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11]

/-- The 3 × 3 determinant of the columns `p`, `q`, `j` of `Y`. -/
def D3 (p q j : Fin 22) : ℤ :=
  Y 0 p * (Y 1 q * Y 2 j - Y 2 q * Y 1 j)
  - Y 0 q * (Y 1 p * Y 2 j - Y 2 p * Y 1 j)
  + Y 0 j * (Y 1 p * Y 2 q - Y 2 p * Y 1 q)

lemma orthZ : ∀ i j : Fin 22, i ≠ j →
    (∑ r, U i r * U j r) * (∑ r, W i r * W j r) * (∑ r, Z i r * Z j r) = 0 := by decide
lemma YZ : ∀ r s, (∑ i, Y r i * Z i s) = 0 := by decide
lemma LZ : ∀ s t, (∑ i, L s i * Z i t) = if s = t then (2520 : ℤ) else 0 := by decide
lemma hdd : ∀ k j, D3 (PP k j) (QQ k j) (JJ k j) ≠ 0 := by decide
lemma hcov : ∀ (k : Fin 12) (j i : Fin 22), (cls i = k ∨ i = j) →
    (i = PP k j ∨ i = QQ k j ∨ i = JJ k j) := by decide
lemma hdist : ∀ k j, PP k j ≠ QQ k j ∧ PP k j ≠ JJ k j ∧ QQ k j ≠ JJ k j := by decide
lemma hdetU : ∀ k k' : Fin 12, k ≠ k' → UC k 0 * UC k' 1 - UC k' 0 * UC k 1 ≠ 0 := by decide
lemma hdetW : ∀ i i' : Fin 22, i ≠ i' → W i 0 * W i' 1 - W i' 0 * W i 1 ≠ 0 := by decide
lemma unz : ∀ i : Fin 22, ¬ (U i 0 = 0 ∧ U i 1 = 0) := by decide
lemma wnz : ∀ i : Fin 22, ¬ (W i 0 = 0 ∧ W i 1 = 0) := by decide
lemma znz : ∀ i : Fin 22, ∃ r, Z i r ≠ 0 := by decide
lemma hUC : ∀ i : Fin 22, UC (cls i) 0 = U i 0 ∧ UC (cls i) 1 = U i 1 := by decide

noncomputable def u : Fin 22 → Fin 2 → ℂ := fun i r => ((U i r : ℤ) : ℂ)
noncomputable def w : Fin 22 → Fin 2 → ℂ := fun i r => ((W i r : ℤ) : ℂ)
noncomputable def z : Fin 22 → Fin 19 → ℂ := fun i r => ((Z i r : ℤ) : ℂ)

lemma tri2 {a1 a2 b1 b2 x y : ℂ} (h1 : a1*x + b1*y = 0) (h2 : a2*x + b2*y = 0)
    (hd : a1*b2 - a2*b1 ≠ 0) : x = 0 ∧ y = 0 := by
  constructor
  · have h : (a1*b2 - a2*b1) * x = 0 := by linear_combination b2*h1 - b1*h2
    exact (mul_eq_zero.mp h).resolve_left hd
  · have h : (a1*b2 - a2*b1) * y = 0 := by linear_combination a1*h2 - a2*h1
    exact (mul_eq_zero.mp h).resolve_left hd

lemma tri3 {a1 a2 a3 b1 b2 b3 e1 e2 e3 x y t : ℂ}
    (h1 : a1*x + b1*y + e1*t = 0) (h2 : a2*x + b2*y + e2*t = 0) (h3 : a3*x + b3*y + e3*t = 0)
    (hd : a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2) ≠ 0) :
    x = 0 ∧ y = 0 ∧ t = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2)) * x = 0 := by
      linear_combination (b2*e3-b3*e2)*h1 - (b1*e3-b3*e1)*h2 + (b1*e2-b2*e1)*h3
    exact (mul_eq_zero.mp h).resolve_left hd
  · have h : (a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2)) * y = 0 := by
      linear_combination (-(a2*e3-a3*e2))*h1 + (a1*e3-a3*e1)*h2 - (a1*e2-a2*e1)*h3
    exact (mul_eq_zero.mp h).resolve_left hd
  · have h : (a1*(b2*e3 - b3*e2) - b1*(a2*e3 - a3*e2) + e1*(a2*b3 - a3*b2)) * t = 0 := by
      linear_combination (a2*b3-a3*b2)*h1 - (a1*b3-a3*b1)*h2 + (a1*b2-a2*b1)*h3
    exact (mul_eq_zero.mp h).resolve_left hd

lemma swapsum (c : Fin 19 → ℂ) (f : Fin 22 → ℂ) (g : Fin 22 → Fin 19 → ℂ) :
    (∑ i, f i * ∑ s, g i s * c s) = ∑ s, (∑ i, f i * g i s) * c s := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring

lemma rel (c : Fin 19 → ℂ) (r : Fin 3) :
    (∑ i, (Y r i : ℂ) * (∑ s, star (z i s) * c s)) = 0 := by
  simp only [z, star_intCast]
  rw [swapsum c (fun i => (Y r i : ℂ)) (fun i s => ((Z i s : ℤ) : ℂ))]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h : (∑ i, (Y r i : ℂ) * ((Z i s : ℤ) : ℂ)) = ((∑ i, Y r i * Z i s : ℤ) : ℂ) := by
    push_cast; ring
  rw [h, YZ r s]; simp

lemma inj (c : Fin 19 → ℂ) (h : ∀ i, (∑ s, star (z i s) * c s) = 0) : c = 0 := by
  funext s
  show c s = 0
  have key : (∑ i, (L s i : ℂ) * (∑ t, star (z i t) * c t)) = (2520 : ℂ) * c s := by
    simp only [z, star_intCast]
    rw [swapsum c (fun i => (L s i : ℂ)) (fun i t => ((Z i t : ℤ) : ℂ))]
    have step : ∀ t, (∑ i, (L s i : ℂ) * ((Z i t : ℤ) : ℂ))
        = ((if s = t then (2520 : ℤ) else 0 : ℤ) : ℂ) := by
      intro t
      have h : (∑ i, (L s i : ℂ) * ((Z i t : ℤ) : ℂ)) = ((∑ i, L s i * Z i t : ℤ) : ℂ) := by
        push_cast; ring
      rw [h, LZ s t]
    simp only [step]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts; simp [Ne.symm hts]
    · intro hs; exact absurd (Finset.mem_univ s) hs
  simp only [h, mul_zero, Finset.sum_const_zero] at key
  exact (mul_eq_zero.mp key.symm).resolve_left (by norm_num)

lemma kill (k0 : Fin 12) (j0 : Fin 22) (Rr : Fin 22 → ℂ)
    (hs : ∀ i, cls i ≠ k0 → i ≠ j0 → Rr i = 0)
    (hrel : ∀ r : Fin 3, (∑ i, (Y r i : ℂ) * Rr i) = 0) : ∀ i, Rr i = 0 := by
  obtain ⟨hpq, hpj, hqj⟩ := hdist k0 j0
  have hsupp : ∀ i, i ≠ PP k0 j0 → i ≠ QQ k0 j0 → i ≠ JJ k0 j0 → Rr i = 0 := by
    intro i h1 h2 h3
    refine hs i ?_ ?_
    · intro hcl
      rcases hcov k0 j0 i (Or.inl hcl) with h|h|h
      exacts [h1 h, h2 h, h3 h]
    · intro hj
      rcases hcov k0 j0 i (Or.inr hj) with h|h|h
      exacts [h1 h, h2 h, h3 h]
  have hexp : ∀ (f : Fin 22 → ℂ),
      (∑ i, f i * Rr i) = f (PP k0 j0) * Rr (PP k0 j0) + f (QQ k0 j0) * Rr (QQ k0 j0)
        + f (JJ k0 j0) * Rr (JJ k0 j0) := by
    intro f
    rw [← Finset.sum_subset
      (Finset.subset_univ ({PP k0 j0, QQ k0 j0, JJ k0 j0} : Finset (Fin 22)))]
    · rw [Finset.sum_insert (by simp [hpq, hpj]), Finset.sum_insert (by simp [hqj]),
        Finset.sum_singleton]
      ring
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rw [hsupp x hx.1 hx.2.1 hx.2.2, mul_zero]
  have h0 := hrel 0; rw [hexp] at h0
  have h1 := hrel 1; rw [hexp] at h1
  have h2 := hrel 2; rw [hexp] at h2
  have hdC :
      (Y 0 (PP k0 j0) : ℂ) * ((Y 1 (QQ k0 j0) : ℂ) * (Y 2 (JJ k0 j0) : ℂ)
          - (Y 2 (QQ k0 j0) : ℂ) * (Y 1 (JJ k0 j0) : ℂ))
      - (Y 0 (QQ k0 j0) : ℂ) * ((Y 1 (PP k0 j0) : ℂ) * (Y 2 (JJ k0 j0) : ℂ)
          - (Y 2 (PP k0 j0) : ℂ) * (Y 1 (JJ k0 j0) : ℂ))
      + (Y 0 (JJ k0 j0) : ℂ) * ((Y 1 (PP k0 j0) : ℂ) * (Y 2 (QQ k0 j0) : ℂ)
          - (Y 2 (PP k0 j0) : ℂ) * (Y 1 (QQ k0 j0) : ℂ)) ≠ 0 := by
    intro hcon
    refine hdd k0 j0 ?_
    have : ((D3 (PP k0 j0) (QQ k0 j0) (JJ k0 j0) : ℤ) : ℂ) = 0 := by
      unfold D3; push_cast; linear_combination hcon
    exact_mod_cast this
  obtain ⟨e1, e2, e3⟩ := tri3 h0 h1 h2 hdC
  intro i
  by_cases hi : i = PP k0 j0
  · rw [hi]; exact e1
  by_cases hi2 : i = QQ k0 j0
  · rw [hi2]; exact e2
  by_cases hi3 : i = JJ k0 j0
  · rw [hi3]; exact e3
  exact hsupp i hi hi2 hi3

/-- The `k = 5` case of `MinUPB224kMinus1`: an unextendible product basis of
cardinality 22 in `C² ⊗ C² ⊗ C^19`. -/
theorem proof :
    ∃ u : Fin 22 → Fin 2 → ℂ, ∃ w : Fin 22 → Fin 2 → ℂ, ∃ z : Fin 22 → Fin 19 → ℂ,
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 → ∀ c : Fin 19 → ℂ, c ≠ 0 →
        ∃ i,
          (∑ r, star (u i r) * a r) *
          (∑ r, star (w i r) * b r) *
          (∑ r, star (z i r) * c r) ≠ 0) := by
  refine ⟨u, w, z, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    refine unz i ⟨?_, ?_⟩
    · have := congrFun h 0; simpa [u] using this
    · have := congrFun h 1; simpa [u] using this
  · intro i h
    refine wnz i ⟨?_, ?_⟩
    · have := congrFun h 0; simpa [w] using this
    · have := congrFun h 1; simpa [w] using this
  · intro i h
    obtain ⟨r, hr⟩ := znz i
    exact hr (by simpa [z] using congrFun h r)
  · intro i j hij
    have h := orthZ i j hij
    have e1 : (∑ r, star (u i r) * u j r) = ((∑ r, U i r * U j r : ℤ) : ℂ) := by
      push_cast; simp [u, star_intCast]
    have e2 : (∑ r, star (w i r) * w j r) = ((∑ r, W i r * W j r : ℤ) : ℂ) := by
      push_cast; simp [w, star_intCast]
    have e3 : (∑ r, star (z i r) * z j r) = ((∑ r, Z i r * Z j r : ℤ) : ℂ) := by
      push_cast; simp [z, star_intCast]
    rw [e1, e2, e3, ← Int.cast_mul, ← Int.cast_mul, h, Int.cast_zero]
  · intro a ha b hb c hc
    by_contra hcon
    push_neg at hcon
    have hPu : ∀ i : Fin 22, (∑ r, star (u i r) * a r)
        = (UC (cls i) 0 : ℂ) * a 0 + (UC (cls i) 1 : ℂ) * a 1 := by
      intro i
      obtain ⟨g0, g1⟩ := hUC i
      rw [g0, g1]
      simp [u, Fin.sum_univ_succ, star_intCast]
    have hQw : ∀ i : Fin 22, (∑ r, star (w i r) * b r)
        = (W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1 := by
      intro i; simp [w, Fin.sum_univ_succ, star_intCast]
    have huniq : ∀ k k' : Fin 12,
        ((UC k 0 : ℂ) * a 0 + (UC k 1 : ℂ) * a 1) = 0 →
        ((UC k' 0 : ℂ) * a 0 + (UC k' 1 : ℂ) * a 1) = 0 → k = k' := by
      intro k k' h1 h2
      by_contra hne
      refine ha ?_
      have hd : ((UC k 0 : ℂ) * (UC k' 1 : ℂ) - (UC k' 0 : ℂ) * (UC k 1 : ℂ)) ≠ 0 := by
        intro hcon2
        refine hdetU k k' hne ?_
        have : ((UC k 0 * UC k' 1 - UC k' 0 * UC k 1 : ℤ) : ℂ) = 0 := by
          push_cast; linear_combination hcon2
        exact_mod_cast this
      obtain ⟨p0, p1⟩ := tri2 h1 h2 hd
      funext r
      fin_cases r
      · exact p0
      · exact p1
    have hquniq : ∀ i i' : Fin 22,
        ((W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1) = 0 →
        ((W i' 0 : ℂ) * b 0 + (W i' 1 : ℂ) * b 1) = 0 → i = i' := by
      intro i i' h1 h2
      by_contra hne
      refine hb ?_
      have hd : ((W i 0 : ℂ) * (W i' 1 : ℂ) - (W i' 0 : ℂ) * (W i 1 : ℂ)) ≠ 0 := by
        intro hcon2
        refine hdetW i i' hne ?_
        have : ((W i 0 * W i' 1 - W i' 0 * W i 1 : ℤ) : ℂ) = 0 := by
          push_cast; linear_combination hcon2
        exact_mod_cast this
      obtain ⟨p0, p1⟩ := tri2 h1 h2 hd
      funext r
      fin_cases r
      · exact p0
      · exact p1
    obtain ⟨k0, hk0⟩ : ∃ k0 : Fin 12,
        ∀ k, ((UC k 0 : ℂ) * a 0 + (UC k 1 : ℂ) * a 1) = 0 → k = k0 := by
      by_cases h : ∃ k : Fin 12, ((UC k 0 : ℂ) * a 0 + (UC k 1 : ℂ) * a 1) = 0
      · obtain ⟨k, hk⟩ := h
        exact ⟨k, fun k' hk' => huniq k' k hk' hk⟩
      · push_neg at h
        exact ⟨0, fun k hk => absurd hk (h k)⟩
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 22,
        ∀ i, ((W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1) = 0 → i = j0 := by
      by_cases h : ∃ i : Fin 22, ((W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1) = 0
      · obtain ⟨i, hi⟩ := h
        exact ⟨i, fun i' hi' => hquniq i' i hi' hi⟩
      · push_neg at h
        exact ⟨0, fun i hi => absurd hi (h i)⟩
    have hsupp : ∀ i, cls i ≠ k0 → i ≠ j0 → (∑ s, star (z i s) * c s) = 0 := by
      intro i h1 h2
      have := hcon i
      rw [hPu i, hQw i] at this
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd (hk0 _ h') h1
        · exact absurd (hj0 _ h') h2
      · exact h
    exact hc (inj c (kill k0 j0 (fun i => ∑ s, star (z i s) * c s) hsupp (rel c)))

end Submissions.MinUPB2219.Cyclic
