#!/usr/bin/env python3
"""C001 — write 42 as a sum of three integer cubes.

Witness format: three whitespace-separated decimal integers `a b c`.
Accepted iff a^3 + b^3 + c^3 == 42.

This is the shape every Conject checker takes: read the witness, decide, print one
`CONJECT_CERT:` line. No network, no imports beyond the standard library, no clock or
randomness — the same witness must always produce the same line.
"""

import json
import sys

TARGET = 42
MAX_ABS = 10**24  # keeps a hostile witness from turning this into a stress test


def emit(ok, reason, canonical=""):
    print("CONJECT_CERT: " + json.dumps(
        {"ok": ok, "reason": reason, "canonical": canonical}, sort_keys=True))
    sys.exit(0)


def main():
    raw = open(sys.argv[1], "rb").read()
    if len(raw) > 4096:
        emit(False, "witness too large")
    try:
        parts = raw.decode("ascii").split()
    except UnicodeDecodeError:
        emit(False, "witness must be ASCII")
    if len(parts) != 3:
        emit(False, f"expected 3 integers, got {len(parts)}")
    try:
        a, b, c = (int(p) for p in parts)
    except ValueError:
        emit(False, "witness entries must be decimal integers")
    if max(abs(a), abs(b), abs(c)) > MAX_ABS:
        emit(False, "witness entries exceed the size bound")

    total = a**3 + b**3 + c**3
    # Canonical form: the multiset of the three integers, so permutations of the same
    # solution deduplicate to one hash.
    canonical = "C001:" + ",".join(str(x) for x in sorted([a, b, c]))
    if total != TARGET:
        emit(False, f"a^3+b^3+c^3 = {total}, expected {TARGET}", canonical)
    emit(True, f"{a}^3 + {b}^3 + {c}^3 = {TARGET}", canonical)


if __name__ == "__main__":
    main()
