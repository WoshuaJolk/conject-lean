#!/usr/bin/env python3
"""Verifier for non-Lean certificate submissions.

A certificate problem owns a checker script under `Certificates/<id>/`. A submission is
a witness file. The checker's only job is to read the witness and print one line:

    CONJECT_CERT: {"ok": true, "reason": "...", "canonical": "<normal form>"}

`canonical` is the witness reduced to a canonical form by the *checker*, not by the
submitter, so it plays the role that the normalized proof term plays on the Lean side:
two submissions of the same witness produce the same `elaborated_term_hash`.

The checker runs with:
  * no network            (Linux user+net namespace, or macOS sandbox-exec)
  * a CPU-seconds rlimit and a wall-clock timeout
  * an address-space rlimit and an output-size rlimit
  * a scratch cwd containing only a copy of the witness
  * no environment inherited except PATH/HOME/LANG

Trust boundary: the checker is repo-owned and reviewed like a canonical statement. The
witness is untrusted. The sandbox protects the runner from the *checker*, since a
checker bug plus a hostile witness is the realistic failure mode.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import platform
import resource
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from conject_common import (  # noqa: E402
    REPO_ROOT,
    fail,
    finish,
    new_verdict,
    record,
    sha256_bytes,
    sha256_file,
    tail,
    utc_now,
)

MARKER = "CONJECT_CERT:"

# A checker earns proof-grade by being cheap to re-run: anyone can repeat 30
# seconds of arithmetic, and a claim nobody repeats is testimony with extra
# steps. A checker that needs more than this is doing the search rather than
# checking a witness, which is why the heavy lane exists and why Jig records an
# artifact verified in it as measurement-grade.
DEFAULT_LIMITS = {
    "wall_sec": 60,
    "cpu_sec": 30,
    "address_space_mb": 2048,
    "output_bytes": 1 << 20,
}

# The ceiling a spec may raise itself to, and only in the heavy lane.
HEAVY_LIMITS = {
    "wall_sec": 2700,
    "cpu_sec": 2400,
    "address_space_mb": 8192,
    "output_bytes": 1 << 24,
}

MACOS_SANDBOX_PROFILE = """(version 1)
(allow default)
(deny network*)
(deny mach-lookup (global-name "com.apple.networkd"))
"""


TRUE_BIN = shutil.which("true") or "/bin/true"


def _probe(argv: list[str]) -> bool:
    """Actually run the wrapper on /bin/true; never assume a sandbox works."""
    try:
        p = subprocess.run(argv + [TRUE_BIN], capture_output=True, timeout=20)
        return p.returncode == 0
    except Exception:
        return False


def netns_wrapper() -> tuple[list[str], str]:
    """Return (argv prefix, description) that removes network access, if we can.

    Three routes, tried in order and each actually probed rather than assumed:

    1. An unprivileged user namespace. The clean option, but Ubuntu 24.04 (and so the
       GitHub Actions runners) ships an AppArmor policy that denies it.
    2. A root network namespace via passwordless sudo, immediately dropping back to the
       calling uid with `setpriv`. The checker still runs unprivileged; only the
       `unshare` gets root, and only long enough to create the empty netns.
    3. macOS `sandbox-exec` with a `deny network*` profile.
    """
    system = platform.system()
    if system == "Linux" and shutil.which("unshare"):
        userns = ["unshare", "--net", "--map-root-user", "--"]
        if _probe(userns):
            return (userns, "linux-userns")
        if shutil.which("sudo") and shutil.which("setpriv"):
            sudo_ns = [
                "sudo", "-n", "unshare", "--net", "--",
                "setpriv", f"--reuid={os.getuid()}", f"--regid={os.getgid()}",
                "--clear-groups", "--",
            ]
            if _probe(sudo_ns):
                return (sudo_ns, "linux-sudo-netns")
    if system == "Darwin" and shutil.which("sandbox-exec"):
        prof = ["sandbox-exec", "-p", MACOS_SANDBOX_PROFILE]
        if _probe(prof):
            return (prof, "macos-sandbox-exec")
    return ([], "none")


def make_preexec(limits: dict):
    def preexec():
        cpu = limits["cpu_sec"]
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))
        mem = limits["address_space_mb"] * 1024 * 1024
        try:
            resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
        except (ValueError, OSError):
            pass  # RLIMIT_AS is not enforceable on some platforms
        out = limits["output_bytes"]
        resource.setrlimit(resource.RLIMIT_FSIZE, (out, out))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        os.setsid()
    return preexec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission", required=True)
    ap.add_argument("--statement")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument(
        "--allow-no-netns", action="store_true",
        default=os.environ.get("CONJECT_ALLOW_NO_NETNS") == "1",
        help="run even if network isolation is unavailable (local development only)")
    args = ap.parse_args()

    started = time.monotonic()
    verdict = new_verdict(kind="certificate", submission=args.submission)
    verdict["term_hash_kind"] = "conject-canonical-witness-v1"

    man_path = pathlib.Path(args.submission)
    if not man_path.is_absolute():
        man_path = REPO_ROOT / man_path
    try:
        manifest = json.loads(man_path.read_text())
    except Exception as e:
        record(verdict, "manifest", False, str(e))
        return finish(fail(verdict, "bad_manifest", str(e)), args.out)

    sid = manifest.get("statement_id")
    verdict["statement_id"] = sid
    if args.statement and args.statement != sid:
        d = f"manifest says {sid!r}, caller asked for {args.statement!r}"
        return finish(fail(record(verdict, "manifest", False, d) or verdict,
                           "statement_id_mismatch", d), args.out)

    problem_dir = REPO_ROOT / "Certificates" / str(sid)
    checker = problem_dir / "checker.py"
    witness = man_path.parent / manifest.get("witness", "")
    if not checker.exists():
        d = f"no checker at Certificates/{sid}/checker.py"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "unknown_statement", d), args.out)
    if not witness.exists():
        d = f"no witness file at {witness}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "missing_witness", d), args.out)
    record(verdict, "manifest", True)

    heavy = os.environ.get("CONJECT_LANE") == "heavy"
    limits = dict(DEFAULT_LIMITS)
    spec_path = problem_dir / "spec.json"
    if spec_path.exists():
        limits.update(json.loads(spec_path.read_text()).get("limits", {}))
    # A spec may raise its own limits, but never past the lane it is running in:
    # the sandbox is what makes a checker's cost knowable in advance.
    ceiling = HEAVY_LIMITS if heavy else DEFAULT_LIMITS
    for k, cap in ceiling.items():
        if limits.get(k, cap) > cap:
            limits[k] = cap
    limits["wall_sec"] = min(limits["wall_sec"], args.timeout)
    verdict["lane"] = "heavy" if heavy else "default"
    verdict["limits"] = limits
    verdict["checker_hash"] = sha256_file(checker)
    verdict["witness_hash"] = sha256_file(witness)
    verdict["decl"] = f"Certificates/{sid}/checker.py"

    prefix, iso = netns_wrapper()
    verdict["network_isolation"] = iso
    if iso == "none" and not args.allow_no_netns:
        d = ("no network isolation available on this host; refusing to run an untrusted "
             "witness (set CONJECT_ALLOW_NO_NETNS=1 to override locally)")
        record(verdict, "sandbox", False, d)
        return finish(fail(verdict, "sandbox_unavailable", d), args.out)
    record(verdict, "sandbox", True, f"isolation={iso}, limits={limits}")

    with tempfile.TemporaryDirectory(prefix="conject-cert-") as tmp:
        tmpdir = pathlib.Path(tmp)
        local_witness = tmpdir / "witness"
        shutil.copyfile(witness, local_witness)
        local_checker = tmpdir / "checker.py"
        shutil.copyfile(checker, local_checker)

        env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": str(tmpdir),
            "LANG": "C.UTF-8",
            "PYTHONHASHSEED": "0",
            "PYTHONDONTWRITEBYTECODE": "1",
        }
        # `env -i` rather than relying on inheritance, because the sudo route sanitizes
        # the environment out from under us. Same command shape on every route.
        cmd = (prefix + ["/usr/bin/env", "-i"]
               + [f"{k}={v}" for k, v in sorted(env.items())]
               + [sys.executable, "checker.py", "witness"])
        t0 = time.monotonic()
        try:
            proc = subprocess.run(
                cmd, cwd=tmpdir, env=env, capture_output=True, text=True,
                errors="replace", timeout=limits["wall_sec"],
                preexec_fn=make_preexec(limits),
            )
        except subprocess.TimeoutExpired:
            d = f"checker exceeded its {limits['wall_sec']}s wall budget"
            record(verdict, "checker_ran", False, d)
            return finish(fail(verdict, "timeout", d), args.out)
        verdict["timings_sec"]["checker"] = round(time.monotonic() - t0, 2)

    verdict["checker_stdout"] = tail(proc.stdout, 2000)
    if proc.returncode != 0:
        d = f"checker exited {proc.returncode}: {tail(proc.stderr, 2000)}"
        record(verdict, "checker_ran", False, d)
        return finish(fail(verdict, "checker_error", d), args.out)
    record(verdict, "checker_ran", True)

    lines = [ln for ln in proc.stdout.splitlines() if ln.startswith(MARKER)]
    if len(lines) != 1:
        d = f"checker must print exactly one {MARKER} line, saw {len(lines)}"
        record(verdict, "checker_protocol", False, d)
        return finish(fail(verdict, "checker_protocol", d), args.out)
    try:
        result = json.loads(lines[0][len(MARKER):].strip())
        ok = bool(result["ok"])
        canonical = str(result.get("canonical", ""))
    except Exception as e:
        d = f"malformed {MARKER} payload: {e}"
        record(verdict, "checker_protocol", False, d)
        return finish(fail(verdict, "checker_protocol", d), args.out)
    record(verdict, "checker_protocol", True)

    verdict["elaborated_term_hash"] = sha256_bytes(canonical.encode())
    verdict["statement_hash"] = sha256_file(checker)

    if not ok:
        d = result.get("reason", "checker rejected the witness")
        record(verdict, "witness_valid", False, d)
        return finish(fail(verdict, "invalid_witness", d), args.out)
    record(verdict, "witness_valid", True, result.get("reason", ""))

    verdict["timings_sec"]["total"] = round(time.monotonic() - started, 2)
    verdict["verdict"] = "green"
    verdict["reason"] = "ok"
    verdict["detail"] = "all checks passed"
    verdict["timestamp"] = utc_now()
    return finish(verdict, args.out)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:
        v = new_verdict(kind="certificate", reason="verifier_error",
                        detail=f"{type(e).__name__}: {e}")
        out = None
        if "--out" in sys.argv:
            out = sys.argv[sys.argv.index("--out") + 1]
        sys.exit(finish(v, out))
