import Mathlib.Data.Finset.Card

/-!
# Cross intersecting set pair systems, and the `1`-cross intersecting refinement

Shared vocabulary for Bollobás' set pair systems and for the `1`-cross intersecting
variant introduced by Füredi, Gyárfás and Király (arXiv:1911.03067,
*Combin. Probab. Comput.* **32** (2023) 15–30).

The ground set is fixed to `ℕ`. This is without loss of generality: a system lives on
finitely many sets, each finite, so its ground set is finite and embeds into `ℕ`, and
every condition below is stated purely in terms of intersections and cardinalities,
all of which are preserved by an injection.
-/

namespace Commons

/-- `OneCrossSPS a b m A B` says that `(A i, B i)` for `i : Fin m` is an
`(a, b)`-**bounded** `1`-**cross intersecting set pair system of size** `m`, in the
sense of Füredi–Gyárfás–Király §3 (conditions i–iii and vi with
`I_cross = {1}`, `I_A = I_B = *`):

* `(A i).card ≤ a`                    — condition ii;
* `(B i).card ≤ b`                    — condition iii;
* `A i ∩ B i = ∅`                     — condition i;
* `(A i ∩ B j).card = 1` for `i ≠ j`  — condition vi at `I_cross = {1}`.

The last clause is quantified over **ordered** pairs `i ≠ j`, matching "`|A_i ∩ B_j| = 1`
for each `i ≠ j`". It subsumes Bollobás' `A i ∩ B j ≠ ∅`, since a set of cardinality `1`
is nonempty.

No injectivity of `i ↦ (A i, B i)` is assumed, and none is needed: if `A i = A j` and
`B i = B j` with `i ≠ j`, then `A i ∩ B j = A i ∩ B i = ∅` has cardinality `0 ≠ 1`, so
distinctness of the pairs is already forced by the last clause.

The maximum `m` for which such a system exists is written `m(a, b, 1)` in the
literature; `m(n, n, 1)` is the case `a = b = n`. -/
def OneCrossSPS (a b m : ℕ) (A B : Fin m → Finset ℕ) : Prop :=
  (∀ i, (A i).card ≤ a) ∧
  (∀ i, (B i).card ≤ b) ∧
  (∀ i, A i ∩ B i = ∅) ∧
  (∀ i j, i ≠ j → (A i ∩ B j).card = 1)

end Commons
