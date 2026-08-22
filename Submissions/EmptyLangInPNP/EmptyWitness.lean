import Commons.PNP

namespace Submissions.EmptyLangInPNP.EmptyWitness

/-- The empty language is decidable in polynomial time (`Commons.PNP.emptyInP`) and
verifiable in polynomial time (`Commons.PNP.emptyInNP`). -/
theorem proof :
    Commons.PNP.InP (∅ : Commons.PNP.Lang) ∧ Commons.PNP.InNP (∅ : Commons.PNP.Lang) :=
  ⟨Commons.PNP.emptyInP, Commons.PNP.emptyInNP⟩

end Submissions.EmptyLangInPNP.EmptyWitness
