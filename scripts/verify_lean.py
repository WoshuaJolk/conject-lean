#!/usr/bin/env python3
"""Deterministic verifier for a Lean submission.

    verify_lean.py --submission Submissions/S001/AliceDirect.json [--out verdict.json]

Pipeline (every step is a compiler invocation or a string comparison; no heuristics):

  1. static policy scan of the submission source
  2. `lake build` the submission module
  3. anti-restatement: elaborate `example : <canonical> := @<their decl>` where
     <canonical> is resolved by name out of `Statements/`, never read from the submission
  4. axiom audit: the transitive axiom set must be a subset of the trusted three
  5. normalized proof-term hash, for telling independent proofs from duplicates

A timeout at any step is a RED verdict, not a hang.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import lean_policy  # noqa: E402
from conject_common import (  # noqa: E402
    ALLOWED_AXIOMS,
    REPO_ROOT,
    fail,
    finish,
    new_verdict,
    record,
    run,
    sha256_file,
    tail,
    toolchain_info,
)

TYPECHECK_TEMPLATE = """\
import {statement_module}
import {submission_module}
import Verify.Guard

/- The canonical type is resolved by name out of `{statement_module}`. This command
   fails unless that name really is declared there, so a submission cannot shadow it. -/
#conject_provenance {statement_const} "{statement_module}"

/- The submitted declaration must genuinely come from the submitted module, not from
   Mathlib or another submission. -/
#conject_provenance {decl} "{submission_module}"

/- THE anti-restatement check. -/
example : {statement_const} := @{decl}
"""

AUDIT_TEMPLATE = """\
import {statement_module}
import {submission_module}
import Verify.Guard

#conject_no_new_axioms "{submission_module}"

#print axioms {decl}

#conject_audit {decl} "{submission_module}" "{sub_prefix}"
#conject_audit {statement_const} "{statement_module}" "{stmt_prefix}"
"""


def module_to_path(mod: str) -> pathlib.Path:
    return REPO_ROOT / (mod.replace(".", "/") + ".lean")


def lean_errors(proc: subprocess.CompletedProcess) -> str:
    """Lean reports diagnostics on stdout; keep only genuine errors."""
    lines = [
        ln
        for ln in (proc.stdout + "\n" + proc.stderr).splitlines()
        if "error:" in ln or ln.startswith("CONJECT_ERROR")
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--submission", required=True, help="path to a submission manifest")
    ap.add_argument("--statement", help="expected statement id (cross-checked)")
    ap.add_argument("--out", help="where to write the verdict JSON")
    ap.add_argument("--timeout", type=int, default=1200, help="total wall budget, seconds")
    ap.add_argument("--work", default=".conject/work")
    args = ap.parse_args()

    started = time.monotonic()

    def remaining() -> float:
        return max(1.0, args.timeout - (time.monotonic() - started))

    verdict = new_verdict(kind="lean", submission=args.submission)
    verdict["toolchain"] = toolchain_info()

    # --- manifest -----------------------------------------------------------
    man_path = pathlib.Path(args.submission)
    if not man_path.is_absolute():
        man_path = REPO_ROOT / man_path
    try:
        manifest = json.loads(man_path.read_text())
    except Exception as e:
        record(verdict, "manifest", False, str(e))
        return finish(fail(verdict, "bad_manifest", str(e)), args.out)

    sid = manifest.get("statement_id")
    module = manifest.get("module")
    decl = manifest.get("decl")
    verdict["statement_id"] = sid
    verdict["decl"] = decl

    if args.statement and args.statement != sid:
        d = f"manifest says {sid!r}, caller asked for {args.statement!r}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "statement_id_mismatch", d), args.out)

    if not (sid and module and decl) or manifest.get("kind") != "lean":
        d = "manifest needs kind=lean plus statement_id, module, decl"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "bad_manifest", d), args.out)

    if not decl.startswith(module + "."):
        d = f"decl {decl!r} is not inside module {module!r}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "bad_manifest", d), args.out)

    statement_module = f"Statements.{sid}"
    statement_const = f"{statement_module}.statement"
    stmt_src = module_to_path(statement_module)
    sub_src = module_to_path(module)

    if not stmt_src.exists():
        d = f"no canonical statement at {stmt_src.relative_to(REPO_ROOT)}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "unknown_statement", d), args.out)
    if not sub_src.exists():
        d = f"no source at {sub_src.relative_to(REPO_ROOT)}"
        record(verdict, "manifest", False, d)
        return finish(fail(verdict, "missing_source", d), args.out)

    record(verdict, "manifest", True)
    verdict["submission_source_hash"] = sha256_file(sub_src)
    verdict["statement_source_hash"] = sha256_file(stmt_src)

    workdir = REPO_ROOT / args.work / f"{sid}__{module.replace('.', '_')}"
    workdir.mkdir(parents=True, exist_ok=True)

    # --- 1. static policy scan ---------------------------------------------
    problems = lean_policy.scan(sub_src.read_text())
    if problems:
        record(verdict, "static_policy", False, "; ".join(problems))
        fail(verdict, "forbidden_syntax", problems[0])
    else:
        record(verdict, "static_policy", True)

    # --- 2. build -----------------------------------------------------------
    t0 = time.monotonic()
    try:
        proc = run(["lake", "build", module, statement_module, "Verify.Guard"],
                   timeout=remaining())
    except subprocess.TimeoutExpired:
        record(verdict, "build", False, "timeout")
        return finish(fail(verdict, "timeout", "lake build exceeded the wall budget"), args.out)
    verdict["timings_sec"]["build"] = round(time.monotonic() - t0, 2)
    if proc.returncode != 0:
        d = tail(proc.stdout + proc.stderr)
        record(verdict, "build", False, d)
        return finish(fail(verdict, "build_failed", d), args.out)
    record(verdict, "build", True)

    # --- 3. anti-restatement -----------------------------------------------
    tc_file = workdir / "TypeCheck.lean"
    tc_file.write_text(
        TYPECHECK_TEMPLATE.format(
            statement_module=statement_module,
            submission_module=module,
            statement_const=statement_const,
            decl=decl,
        )
    )
    verdict["typecheck_file"] = str(tc_file.relative_to(REPO_ROOT))
    t0 = time.monotonic()
    try:
        proc = run(["lake", "env", "lean", str(tc_file)], timeout=remaining())
    except subprocess.TimeoutExpired:
        record(verdict, "anti_restatement", False, "timeout")
        return finish(fail(verdict, "timeout", "anti-restatement check timed out"), args.out)
    verdict["timings_sec"]["anti_restatement"] = round(time.monotonic() - t0, 2)
    if proc.returncode != 0:
        d = tail(lean_errors(proc) or proc.stdout + proc.stderr)
        record(verdict, "anti_restatement", False, d)
        if "environment already contains" in d:
            reason = "shadowed_statement"
        elif "CONJECT_ERROR: provenance" in proc.stdout:
            reason = "provenance"
        else:
            reason = "restatement"
        fail(verdict, reason,
             f"`example : {statement_const} := @{decl}` did not elaborate: {d}")
    else:
        record(verdict, "anti_restatement", True,
               f"example : {statement_const} := @{decl}")

    # --- 4/5. axiom audit + term hash --------------------------------------
    sub_prefix = workdir / "sub"
    stmt_prefix = workdir / "stmt"
    audit_file = workdir / "Audit.lean"
    audit_file.write_text(
        AUDIT_TEMPLATE.format(
            statement_module=statement_module,
            submission_module=module,
            statement_const=statement_const,
            decl=decl,
            sub_prefix=str(sub_prefix),
            stmt_prefix=str(stmt_prefix),
        )
    )
    t0 = time.monotonic()
    try:
        proc = run(["lake", "env", "lean", str(audit_file)], timeout=remaining())
    except subprocess.TimeoutExpired:
        record(verdict, "axioms", False, "timeout")
        return finish(fail(verdict, "timeout", "axiom audit timed out"), args.out)
    verdict["timings_sec"]["audit"] = round(time.monotonic() - t0, 2)

    print_axioms_line = next(
        (ln for ln in proc.stdout.splitlines() if "depends on axioms" in ln
         or "does not depend on any axioms" in ln),
        "",
    )
    verdict["print_axioms"] = print_axioms_line.strip()

    sub_json = sub_prefix.with_suffix(".json")
    if proc.returncode != 0 or not sub_json.exists():
        d = tail(lean_errors(proc) or proc.stdout + proc.stderr)
        record(verdict, "axioms", False, d)
        record(verdict, "no_new_axioms", False, d)
        return finish(fail(verdict, "audit_failed", d), args.out)
    record(verdict, "no_new_axioms", True)

    audit = json.loads(sub_json.read_text())
    axioms = sorted(audit.get("axioms", []))
    verdict["axioms"] = axioms
    extra = sorted(set(axioms) - ALLOWED_AXIOMS)
    if extra:
        d = f"axioms outside the trusted base: {extra}"
        record(verdict, "axioms", False, d)
        reason = "sorry" if "sorryAx" in extra else (
            "native_decide" if any(a.startswith("Lean.ofReduce") for a in extra)
            else "disallowed_axiom")
        fail(verdict, reason, d)
    else:
        record(verdict, "axioms", True, f"{axioms} ⊆ {sorted(ALLOWED_AXIOMS)}")

    term_file = pathlib.Path(audit["term_file"])
    verdict["elaborated_term_hash"] = sha256_file(term_file)
    verdict["term_bytes"] = audit.get("term_bytes")
    if audit.get("term_truncated"):
        verdict["term_hash_kind"] = "conject-normalized-v1-truncated"

    stmt_json = stmt_prefix.with_suffix(".json")
    if stmt_json.exists():
        stmt_audit = json.loads(stmt_json.read_text())
        verdict["statement_hash"] = sha256_file(pathlib.Path(stmt_audit["term_file"]))

    # --- verdict ------------------------------------------------------------
    verdict["timings_sec"]["total"] = round(time.monotonic() - started, 2)
    if all(c["ok"] for c in verdict["checks"].values()):
        verdict["verdict"] = "green"
        verdict["reason"] = "ok"
        verdict["detail"] = "all checks passed"
    return finish(verdict, args.out)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:  # a crashing verifier must still say RED
        v = new_verdict(kind="lean", reason="verifier_error", detail=f"{type(e).__name__}: {e}")
        out = None
        argv = sys.argv
        if "--out" in argv:
            out = argv[argv.index("--out") + 1]
        sys.exit(finish(v, out))
