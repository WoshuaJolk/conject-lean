import Commons.PNP

/-!
# EmptyLangInPNP — the empty language is in both P and NP

A small, true statement in the vocabulary of `Statements.PvsNP`, used to smoke-test the
`Commons.PNP` definitions and the verification pipeline before posing the root: it is
provable (unlike the root), and a green artifact against it shows `InP`/`InNP` are not
vacuous — some language actually satisfies each.
-/

namespace Statements.EmptyLangInPNP

/-- The canonical proposition. This is the type the verifier demands. -/
abbrev statement : Prop :=
  Commons.PNP.InP (∅ : Commons.PNP.Lang) ∧ Commons.PNP.InNP (∅ : Commons.PNP.Lang)

/-- The open target. A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.EmptyLangInPNP
