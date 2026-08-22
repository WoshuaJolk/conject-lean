namespace Submissions.EmptyLangInPNP.TrivialRestatement

/-- A must-fail control: proves a trivially true, unrelated proposition and tries to
pass it off as the statement. Must red with `restatement` (the anti-restatement bridge
fails to typecheck `@proof` at `Statements.EmptyLangInPNP.statement`), not green. -/
theorem proof : True := trivial

end Submissions.EmptyLangInPNP.TrivialRestatement
