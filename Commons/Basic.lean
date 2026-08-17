/-
`Commons` holds curated definitions that canonical statements and submissions are
allowed to share. Anything here is part of the trusted vocabulary: a submission may
`import Commons.*` and the verifier will treat those constants as opaque shared
names rather than inlining them into the proof-term hash.

Adding to `Commons` changes what statements *mean*, so it is the one directory that
needs human review on every change.
-/
namespace Commons

/-- Marker used by the verifier's self-test to confirm `Commons` is on the import path. -/
def schemaVersion : Nat := 1

end Commons
