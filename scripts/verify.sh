#!/usr/bin/env bash
# Conject verification entrypoint.
#
#   scripts/verify.sh --submission Submissions/S001/AliceDirect.json [--out verdict.json]
#
# Dispatches to the Lean verifier or the certificate verifier based on the manifest's
# `kind`, and enforces an outer wall clock. Exit 0 = green, 1 = red, 2 = usage error.
# A timeout is always a red verdict with a written JSON file, never a hang.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

SUBMISSION=""
STATEMENT=""
OUT=""
TIMEOUT="${CONJECT_TIMEOUT:-1200}"

while [ $# -gt 0 ]; do
  case "$1" in
    --submission) SUBMISSION="$2"; shift 2 ;;
    --statement)  STATEMENT="$2";  shift 2 ;;
    --out)        OUT="$2";        shift 2 ;;
    --timeout)    TIMEOUT="$2";    shift 2 ;;
    -h|--help)
      sed -n '2,10p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "conject: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

if [ -z "$SUBMISSION" ]; then
  echo "conject: --submission is required" >&2
  exit 2
fi

if [ ! -f "$ROOT/$SUBMISSION" ] && [ ! -f "$SUBMISSION" ]; then
  echo "conject: no such manifest: $SUBMISSION" >&2
  exit 2
fi

KIND="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("kind",""))' \
        "$([ -f "$ROOT/$SUBMISSION" ] && echo "$ROOT/$SUBMISSION" || echo "$SUBMISSION")")"

case "$KIND" in
  lean) DRIVER="$ROOT/scripts/verify_lean.py" ;;
  certificate) DRIVER="$ROOT/scripts/verify_cert.py" ;;
  *) echo "conject: manifest kind must be 'lean' or 'certificate', got '$KIND'" >&2; exit 2 ;;
esac

ARGS=(--submission "$SUBMISSION" --timeout "$TIMEOUT")
[ -n "$STATEMENT" ] && ARGS+=(--statement "$STATEMENT")
[ -n "$OUT" ] && ARGS+=(--out "$OUT")

# Outer watchdog: the drivers police their own budget, this catches a wedged driver.
# Give it 60s of slack so the driver's own timeout handling wins when it can.
HARD=$((TIMEOUT + 60))
if command -v timeout >/dev/null 2>&1; then
  RUNNER=(timeout -k 10 "$HARD")
elif command -v gtimeout >/dev/null 2>&1; then
  RUNNER=(gtimeout -k 10 "$HARD")
else
  RUNNER=(env)   # no watchdog available; the driver's own budget is the only limit
fi

cd "$ROOT"
"${RUNNER[@]}" python3 "$DRIVER" "${ARGS[@]}"
STATUS=$?

# 124 is GNU timeout's signal that it fired. Any status above 1 means the driver never
# got to write a verdict, so synthesize a red one here.
if [ "$STATUS" -gt 1 ]; then
  if [ "$STATUS" -eq 124 ] || [ "$STATUS" -eq 137 ]; then
    REASON="timeout"
  else
    REASON="verifier_error"
  fi
  python3 - "$OUT" "$SUBMISSION" "$REASON" "$STATUS" <<'PY'
import json, sys, datetime, pathlib
out, sub, reason, status = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
v = {
  "schema": "conject.verdict.v1",
  "verdict": "red",
  "reason": reason,
  "detail": f"verify.sh watchdog: driver exited with status {status}",
  "submission": sub,
  "decl": None,
  "axioms": [],
  "elaborated_term_hash": None,
  "timestamp": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
}
text = json.dumps(v, indent=2)
if out:
    p = pathlib.Path(out); p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text + "\n")
print(text)
PY
  exit 1
fi

exit "$STATUS"
