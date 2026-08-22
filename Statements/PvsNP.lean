import Commons.PNP

/-!
# PvsNP — is P equal to NP?

This module is the **single source of truth** for what P vs NP means here. The
verifier reads `Statements.PvsNP.statement` and nothing else; a submission never gets
to supply its own copy of the statement.

`Commons.PNP` fixes the model: decision problems are sets of bitstrings (`Lang`), `P` is
decidability by a `Turing.TM2` multi-tape Turing machine (Mathlib's own
`Turing.TM2ComputableInPolyTime`) running in time bounded by a polynomial in the input
length, and `NP` is the certificate/verifier definition — a polynomial bound on
certificate length plus a poly-time verifier of (instance, certificate) pairs (Sipser,
*Introduction to the Theory of Computation*, 3rd ed., §7.3, Definition 7.19; the
question itself: S. A. Cook, "The complexity of theorem proving procedures", STOC 1971,
https://doi.org/10.1145/800157.805047, and the Clay Mathematics Institute problem
description by S. Cook, "The P versus NP Problem", 2000).

Submissions **must not** import this module (the verifier rejects them if they do),
because `target` below is closed with `sorry`.
-/

namespace Statements.PvsNP

/-- The canonical proposition: the set of polynomial-time-decidable languages equals the
set of polynomial-time-verifiable languages. This is the full statement — both
directions — even though `Commons.PNP.P ⊆ Commons.PNP.NP` is the easy half; the root is
posed as the equality because that is how the literature states the question. -/
abbrev statement : Prop := Commons.PNP.P = Commons.PNP.NP

/-- The open target. Replacing this `sorry` is not how the problem is solved: a
submission proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.PvsNP
