"""Shared helpers for the Conject verifiers.

Both the Lean path (`verify_lean.py`) and the certificate path (`verify_cert.py`)
emit the same verdict shape, so downstream consumers never branch on submission kind.
"""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import pathlib
import subprocess
import sys

VERDICT_SCHEMA = "conject.verdict.v1"

# The only axioms a green Lean submission may depend on. This is exactly Mathlib's
# standard trusted base.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return sha256_bytes(path.read_bytes())


def utc_now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def new_verdict(**kw) -> dict:
    """A verdict starts RED. Every check has to actively turn it green."""
    v = {
        "schema": VERDICT_SCHEMA,
        "verdict": "red",
        "reason": "not_run",
        "detail": "",
        "kind": "lean",
        "statement_id": None,
        "submission": None,
        "decl": None,
        "axioms": [],
        "elaborated_term_hash": None,
        "statement_hash": None,
        "term_hash_kind": "conject-normalized-v1",
        "checks": {},
        "toolchain": {},
        "timings_sec": {},
        "timestamp": utc_now(),
    }
    v.update(kw)
    return v


def finish(verdict: dict, out_path: str | None) -> int:
    """Write the verdict, print it, and return the process exit code.

    Exit 0 for green, 1 for red. A crash in the driver itself must never reach here;
    callers wrap `main` so that an unexpected exception still produces a red verdict.
    """
    text = json.dumps(verdict, indent=2, sort_keys=False)
    if out_path:
        p = pathlib.Path(out_path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text + "\n")
    print(text)
    return 0 if verdict["verdict"] == "green" else 1


def record(verdict: dict, name: str, ok: bool, detail: str = "") -> bool:
    verdict["checks"][name] = {"ok": ok, "detail": detail}
    return ok


def fail(verdict: dict, reason: str, detail: str = "") -> dict:
    """Set the primary failure reason, keeping the first one that fired."""
    if verdict["reason"] in ("not_run", "ok"):
        verdict["reason"] = reason
        verdict["detail"] = detail
    return verdict


def run(cmd, cwd=None, timeout=None, env=None):
    """Run a command, capturing output. Raises subprocess.TimeoutExpired on timeout."""
    return subprocess.run(
        cmd,
        cwd=cwd or REPO_ROOT,
        timeout=timeout,
        env=env or os.environ.copy(),
        capture_output=True,
        text=True,
        errors="replace",
    )


def tail(s: str, n: int = 4000) -> str:
    s = s.strip()
    return s if len(s) <= n else "…" + s[-n:]


def toolchain_info() -> dict:
    info = {}
    tc = REPO_ROOT / "lean-toolchain"
    if tc.exists():
        info["lean_toolchain"] = tc.read_text().strip()
    manifest = REPO_ROOT / "lake-manifest.json"
    if manifest.exists():
        try:
            data = json.loads(manifest.read_text())
            for pkg in data.get("packages", []):
                if pkg.get("name") == "mathlib":
                    info["mathlib_rev"] = pkg.get("rev")
            info["manifest_hash"] = sha256_file(manifest)
        except Exception:
            pass
    return info


def die(msg: str) -> None:
    print(f"conject: {msg}", file=sys.stderr)
    sys.exit(2)
