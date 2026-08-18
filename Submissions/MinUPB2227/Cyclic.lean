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
# MinUPB2227 — an unextendible product basis of cardinality 30 in `C² ⊗ C² ⊗ C^27`

The witness is the `k = 7` member of an explicit family built by iterating a local
"block insertion" surgery on the verified `k = 2` witness. Every entry is an integer of
absolute value at most 12.

The unextendibility proof is dual. Let `Z` be the `30 × 27` integer matrix of third factors.
We supply

* `Y : Fin 3 → Fin 30 → ℤ` with `Y * Z = 0` — a basis of the space of linear relations
  among the 30 vectors (their rank is 27 = 30 − 3, so the relation space is exactly 3-dimensional);
* `L : Fin 27 → Fin 30 → ℤ` with `L * Z = 600 * I` — an integer left inverse, so `Z` is injective.

For nonzero `a : C²` the states annihilated by `a` form a single `u`-parallel class, and for
nonzero `b : C²` a single `w`-parallel class (all of which are singletons here). Hence at most
three of the numbers `⟨zᵢ, c⟩` can be nonzero, and their index set `T` lies in
`class(k₀) ∪ {j₀}`. The three relations then read `Σ_{i ∈ T} Y r i · ⟨zᵢ, c⟩ = 0`, a
3 × 3 system whose determinant `D3` is nonzero — that is the table `hdd`, checked by `decide`.
So every `⟨zᵢ, c⟩` vanishes, and `L` forces `c = 0`.

All finite combinatorics (orthogonality of the 30 product states, `Y * Z = 0`, `L * Z = 600 I`,
the determinant table, the covering property of the index table, and the pairwise
non-parallelism of the `u`- and `w`-directions) are integer statements closed by `decide`.
-/

namespace Submissions.MinUPB2227.Cyclic

def U : Fin 30 → Fin 2 → ℤ := ![![1, 1],
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
   ![(-6), 1],
   ![1, 7],
   ![1, 7],
   ![(-7), 1],
   ![(-7), 1],
   ![1, 8],
   ![1, 8],
   ![(-8), 1],
   ![(-8), 1]]

def W : Fin 30 → Fin 2 → ℤ := ![![1, 1],
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
   ![1, 12],
   ![(-11), 1],
   ![1, 13],
   ![(-10), 1],
   ![1, 14],
   ![(-13), 1],
   ![1, 15],
   ![(-12), 1],
   ![(-2), 1],
   ![(-15), 1],
   ![(-3), 1],
   ![(-14), 1]]

def Z : Fin 30 → Fin 27 → ℤ := ![![0, 0, (-6), (-5), 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
   ![5, (-4), (-2), 0, 0, 0, 0, (-2), 12, 1, 0, (-2), (-1), 1, 0, (-2), (-1), 1, 0, (-2), (-1), 1, 0, (-2), (-1), 1, 0],
   ![0, (-3), 6, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, (-1), 1, (-6), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 2, 2, (-3), (-3), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![12, 12, 6, (-6), 6, 0, 0, (-12), (-2), 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, (-2), 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, (-1), (-6), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 1, 0, 2, (-12), (-1), 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 1, (-12), (-2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, (-1), 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, (-2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, (-1), 2, 0, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, (-2), 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, (-1), 2, 0, 1],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, (-2), 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, (-2)],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def Y : Fin 3 → Fin 30 → ℤ := ![![(-25), 60, 0, (-23), 105, 0, (-5), (-9), (-655), (-4035), (-120), (-10), 120, 1465, (-180), 120, 240, 540, (-240), 120, 360, 660, (-300), 120, 480, 780, (-360), 120, 600, 900],
   ![25, 60, 0, 32, (-45), 50, (-5), 56, 295, 1815, (-120), (-60), (-480), 1565, (-180), 720, (-360), 1740, (-240), 720, (-240), 1860, (-300), 720, (-120), 1980, (-360), 720, 0, 2100],
   ![(-14), (-102), 6, (-19), 6, (-34), 6, (-37), (-50), (-306), 186, (-26), (-690), (-2186), 300, 324, (-930), 162, 414, 336, (-1170), (-42), 528, 348, (-1410), (-246), 642, 360, (-1650), (-450)]]

def L : Fin 27 → Fin 30 → ℤ := ![![(-562), 144, 48, (-620), 1578, (-572), 18, (-740), (-10030), (-61758), 168, 32, 0, (-2098), 120, (-288), 0, (-864), 72, (-192), 0, (-576), 24, (-96), 0, (-288), (-24), 0, 0, 0],
   ![(-200), 0, 0, (-220), 600, 0, 0, (-60), (-3800), (-23400), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-100), 0, 0, (-20), 300, 0, 0, (-60), (-1900), (-11700), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 30, (-300), 0, 0, 90, 1800, 11100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 30, 300, 0, 0, 90, (-1800), (-11100), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, (-600), (-3600), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-912), 144, 48, (-960), 2928, (-672), (-32), (-960), (-18480), (-113808), 168, 32, 0, (-2048), 120, (-288), 0, (-864), 72, (-192), 0, (-576), 24, (-96), 0, (-288), (-24), 0, 0, 0],
   ![600, 0, 0, 660, (-1800), 600, 0, 780, 11400, 70200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![50, 0, 0, 55, (-150), 50, 0, 65, 950, 5850, 0, (-50), 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-600), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-912), 144, 48, (-960), 2928, (-672), (-32), (-960), (-18480), (-113808), (-432), 32, 1200, 5152, 120, (-288), 0, (-264), 72, (-192), 0, (-576), 24, (-96), 0, (-288), (-24), 0, 0, 0],
   ![(-50), 0, 0, (-55), 150, (-50), 0, (-65), (-950), (-5850), 0, 50, 600, (-100), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![50, 0, 0, 55, (-150), 50, 0, 65, 950, 5850, 0, (-50), (-600), 100, 0, 600, 0, 1200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-912), 144, 48, (-960), 2928, (-672), (-32), (-960), (-18480), (-113808), (-432), 32, 1200, 5152, (-480), (-288), 1200, 336, 72, (-192), 0, 24, 24, (-96), 0, (-288), (-24), 0, 0, 0],
   ![(-50), 0, 0, (-55), 150, (-50), 0, (-65), (-950), (-5850), 0, 50, 600, (-100), 0, (-600), 600, (-1200), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![50, 0, 0, 55, (-150), 50, 0, 65, 950, 5850, 0, (-50), (-600), 100, 0, 600, (-600), 1200, 0, 600, 0, 1200, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 600, 0, 0, 0, 0, 0, 0, 0, 0],
   ![(-912), 144, 48, (-960), 2928, (-672), (-32), (-960), (-18480), (-113808), (-432), 32, 1200, 5152, (-480), (-288), 1200, 336, (-528), (-192), 1200, 624, 24, (-96), 0, 312, (-24), 0, 0, 0],
   ![(-50), 0, 0, (-55), 150, (-50), 0, (-65), (-950), (-5850), 0, 50, 600, (-100), 0, (-600), 600, (-1200), 0, (-600), 600, (-1200), 0, 0, 0, 0, 0, 0, 0, 0],
   ![50, 0, 0, 55, (-150), 50, 0, 65, 950, 5850, 0, (-50), (-600), 100, 0, 600, (-600), 1200, 0, 600, (-600), 1200, 0, 600, 0, 1200, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 600, 0, 0, 0, 0],
   ![4210, (-120), (-240), 4460, (-13290), 3260, 110, 4580, 83950, 516990, 960, (-160), (-3600), (-11310), 600, 1440, (-2400), 1320, 240, 960, (-1200), 1080, (-120), 480, 0, 840, 120, 0, 0, 0],
   ![(-50), 0, 0, (-55), 150, (-50), 0, (-65), (-950), (-5850), 0, 50, 600, (-100), 0, (-600), 600, (-1200), 0, (-600), 600, (-1200), 0, (-600), 600, (-1200), 0, 0, 0, 0],
   ![(-4666), 192, 264, (-4940), 14754, (-3596), (-126), (-5060), (-93190), (-573894), (-1176), 176, 4200, 13886, (-840), (-1584), 3000, (-1152), (-504), (-1056), 1800, (-768), (-168), (-528), 600, (-384), 168, 0, 0, 0],
   ![5122, (-264), (-288), 5420, (-16218), 3932, 142, 5540, 102430, 630798, 1392, (-192), (-4800), (-16462), 1080, 1728, (-3600), 984, 768, 1152, (-2400), 456, 456, 576, (-1200), (-72), 144, 0, 0, 0]]

def UC : Fin 16 → Fin 2 → ℤ := ![![1, 1],
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
   ![(-6), 1],
   ![1, 7],
   ![(-7), 1],
   ![1, 8],
   ![(-8), 1]]

def PP : Fin 16 → Fin 30 → Fin 30 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   ![0, 1, 2, 3, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
   ![0, 1, 2, 3, 4, 5, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
   ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 0, 22, 22, 22, 22, 22, 22],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 24, 24, 24, 24],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 0, 0, 26, 26],
   ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 0]]

def QQ : Fin 16 → Fin 30 → Fin 30 := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   ![2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
   ![4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
   ![6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
   ![1, 1, 2, 3, 4, 5, 6, 7, 1, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8],
   ![1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
   ![10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],
   ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
   ![14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15],
   ![16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17],
   ![18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19],
   ![20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21],
   ![22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23],
   ![24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25],
   ![26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27],
   ![28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28]]

def JJ : Fin 16 → Fin 30 → Fin 30 := ![![2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![3, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![5, 5, 5, 5, 5, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![7, 7, 7, 7, 7, 7, 7, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 23, 24, 25, 26, 27, 28, 29],
   ![23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 25, 26, 27, 28, 29],
   ![25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 27, 28, 29],
   ![27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 29],
   ![29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29]]

def cls : Fin 30 → Fin 16 := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15]

/-- The 3 × 3 determinant of the columns `p`, `q`, `j` of `Y`. -/
def D3 (p q j : Fin 30) : ℤ :=
  Y 0 p * (Y 1 q * Y 2 j - Y 2 q * Y 1 j)
  - Y 0 q * (Y 1 p * Y 2 j - Y 2 p * Y 1 j)
  + Y 0 j * (Y 1 p * Y 2 q - Y 2 p * Y 1 q)

lemma orthZ : ∀ i j : Fin 30, i ≠ j →
    (∑ r, U i r * U j r) * (∑ r, W i r * W j r) * (∑ r, Z i r * Z j r) = 0 := by decide
lemma YZ : ∀ r s, (∑ i, Y r i * Z i s) = 0 := by decide
lemma LZ : ∀ s t, (∑ i, L s i * Z i t) = if s = t then (600 : ℤ) else 0 := by decide
lemma hdd : ∀ k j, D3 (PP k j) (QQ k j) (JJ k j) ≠ 0 := by decide
lemma hcov : ∀ (k : Fin 16) (j i : Fin 30), (cls i = k ∨ i = j) →
    (i = PP k j ∨ i = QQ k j ∨ i = JJ k j) := by decide
lemma hdist : ∀ k j, PP k j ≠ QQ k j ∧ PP k j ≠ JJ k j ∧ QQ k j ≠ JJ k j := by decide
lemma hdetU : ∀ k k' : Fin 16, k ≠ k' → UC k 0 * UC k' 1 - UC k' 0 * UC k 1 ≠ 0 := by decide
lemma hdetW : ∀ i i' : Fin 30, i ≠ i' → W i 0 * W i' 1 - W i' 0 * W i 1 ≠ 0 := by decide
lemma unz : ∀ i : Fin 30, ¬ (U i 0 = 0 ∧ U i 1 = 0) := by decide
lemma wnz : ∀ i : Fin 30, ¬ (W i 0 = 0 ∧ W i 1 = 0) := by decide
lemma znz : ∀ i : Fin 30, ∃ r, Z i r ≠ 0 := by decide
lemma hUC : ∀ i : Fin 30, UC (cls i) 0 = U i 0 ∧ UC (cls i) 1 = U i 1 := by decide

noncomputable def u : Fin 30 → Fin 2 → ℂ := fun i r => ((U i r : ℤ) : ℂ)
noncomputable def w : Fin 30 → Fin 2 → ℂ := fun i r => ((W i r : ℤ) : ℂ)
noncomputable def z : Fin 30 → Fin 27 → ℂ := fun i r => ((Z i r : ℤ) : ℂ)

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

lemma swapsum (c : Fin 27 → ℂ) (f : Fin 30 → ℂ) (g : Fin 30 → Fin 27 → ℂ) :
    (∑ i, f i * ∑ s, g i s * c s) = ∑ s, (∑ i, f i * g i s) * c s := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring

lemma rel (c : Fin 27 → ℂ) (r : Fin 3) :
    (∑ i, (Y r i : ℂ) * (∑ s, star (z i s) * c s)) = 0 := by
  simp only [z, star_intCast]
  rw [swapsum c (fun i => (Y r i : ℂ)) (fun i s => ((Z i s : ℤ) : ℂ))]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h : (∑ i, (Y r i : ℂ) * ((Z i s : ℤ) : ℂ)) = ((∑ i, Y r i * Z i s : ℤ) : ℂ) := by
    push_cast; ring
  rw [h, YZ r s]; simp

lemma inj (c : Fin 27 → ℂ) (h : ∀ i, (∑ s, star (z i s) * c s) = 0) : c = 0 := by
  funext s
  show c s = 0
  have key : (∑ i, (L s i : ℂ) * (∑ t, star (z i t) * c t)) = (600 : ℂ) * c s := by
    simp only [z, star_intCast]
    rw [swapsum c (fun i => (L s i : ℂ)) (fun i t => ((Z i t : ℤ) : ℂ))]
    have step : ∀ t, (∑ i, (L s i : ℂ) * ((Z i t : ℤ) : ℂ))
        = ((if s = t then (600 : ℤ) else 0 : ℤ) : ℂ) := by
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

lemma kill (k0 : Fin 16) (j0 : Fin 30) (Rr : Fin 30 → ℂ)
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
  have hexp : ∀ (f : Fin 30 → ℂ),
      (∑ i, f i * Rr i) = f (PP k0 j0) * Rr (PP k0 j0) + f (QQ k0 j0) * Rr (QQ k0 j0)
        + f (JJ k0 j0) * Rr (JJ k0 j0) := by
    intro f
    rw [← Finset.sum_subset
      (Finset.subset_univ ({PP k0 j0, QQ k0 j0, JJ k0 j0} : Finset (Fin 30)))]
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

/-- The `k = 7` case of `MinUPB224kMinus1`: an unextendible product basis of
cardinality 30 in `C² ⊗ C² ⊗ C^27`. -/
theorem proof :
    ∃ u : Fin 30 → Fin 2 → ℂ, ∃ w : Fin 30 → Fin 2 → ℂ, ∃ z : Fin 30 → Fin 27 → ℂ,
      (∀ i, u i ≠ 0) ∧
      (∀ i, w i ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j →
        (∑ r, star (u i r) * u j r) *
        (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
      (∀ a : Fin 2 → ℂ, a ≠ 0 → ∀ b : Fin 2 → ℂ, b ≠ 0 → ∀ c : Fin 27 → ℂ, c ≠ 0 →
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
    have hPu : ∀ i : Fin 30, (∑ r, star (u i r) * a r)
        = (UC (cls i) 0 : ℂ) * a 0 + (UC (cls i) 1 : ℂ) * a 1 := by
      intro i
      obtain ⟨g0, g1⟩ := hUC i
      rw [g0, g1]
      simp [u, Fin.sum_univ_succ, star_intCast]
    have hQw : ∀ i : Fin 30, (∑ r, star (w i r) * b r)
        = (W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1 := by
      intro i; simp [w, Fin.sum_univ_succ, star_intCast]
    have huniq : ∀ k k' : Fin 16,
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
    have hquniq : ∀ i i' : Fin 30,
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
    obtain ⟨k0, hk0⟩ : ∃ k0 : Fin 16,
        ∀ k, ((UC k 0 : ℂ) * a 0 + (UC k 1 : ℂ) * a 1) = 0 → k = k0 := by
      by_cases h : ∃ k : Fin 16, ((UC k 0 : ℂ) * a 0 + (UC k 1 : ℂ) * a 1) = 0
      · obtain ⟨k, hk⟩ := h
        exact ⟨k, fun k' hk' => huniq k' k hk' hk⟩
      · push_neg at h
        exact ⟨0, fun k hk => absurd hk (h k)⟩
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 30,
        ∀ i, ((W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1) = 0 → i = j0 := by
      by_cases h : ∃ i : Fin 30, ((W i 0 : ℂ) * b 0 + (W i 1 : ℂ) * b 1) = 0
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

end Submissions.MinUPB2227.Cyclic
